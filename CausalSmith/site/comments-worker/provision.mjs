#!/usr/bin/env node
/**
 * One-off, maintainer-run provisioning of per-paper comment discussions.
 *
 * The paper pages resolve their comment thread by DISCUSSION NUMBER, and a
 * visitor's browser is never allowed to create a discussion (that would make a
 * random reader the thread's owner). So the maintainer creates one discussion
 * per paper here, ONCE, with a write-scoped token, and records the number in
 * `src/lib/comments/discussions.json`. The deployed worker keeps its read-only
 * token; this script's token never touches the worker or the site.
 *
 * Idempotent: papers already in discussions.json are left untouched, and a
 * pre-run scan of existing discussion titles avoids creating a duplicate for a
 * thread that exists but is missing from the JSON.
 *
 * Usage (from site/):
 *   GITHUB_TOKEN=<PAT with Discussions: write on the repo> \
 *   GITHUB_REPO=Jiyuan-Tan/CausalSmith \
 *   DISCUSSION_CATEGORY="Paper comments" \
 *     node comments-worker/provision.mjs
 *
 * Paper ids come from the freshly built dist/papers/<id>/ directory names — the
 * exact set of pages that shipped, so a thread is never provisioned for a paper
 * that is not actually published. Run `npm run build` first.
 */

import { readdirSync, readFileSync, writeFileSync, existsSync, statSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));
const siteRoot = join(here, "..");
const distPapers = join(siteRoot, "dist", "papers");
const mapPath = join(siteRoot, "src", "lib", "comments", "discussions.json");

const token = process.env.GITHUB_TOKEN;
const repo = process.env.GITHUB_REPO || "";
const categoryName = process.env.DISCUSSION_CATEGORY || "Paper comments";
const [owner, name] = repo.split("/");

if (!token || !owner || !name) {
  console.error(
    "Set GITHUB_TOKEN (Discussions: write) and GITHUB_REPO=owner/name before running.",
  );
  process.exit(1);
}
if (!existsSync(distPapers)) {
  console.error(`No built pages at ${distPapers} — run \`npm run build\` first.`);
  process.exit(1);
}

async function gql(query, variables) {
  const res = await fetch("https://api.github.com/graphql", {
    method: "POST",
    headers: {
      Authorization: `Bearer ${token}`,
      "Content-Type": "application/json",
      "User-Agent": "causalsmith-provision",
    },
    body: JSON.stringify({ query, variables }),
  });
  const data = await res.json();
  if (data.errors) throw new Error(data.errors.map((e) => e.message).join("; "));
  if (!data.data) throw new Error(`GitHub API returned no data (HTTP ${res.status})`);
  return data.data;
}

/**
 * Every existing discussion by title → list of { number, url, author } (paged).
 *
 * The author is load-bearing: a visitor's browser can `createDiscussion`
 * directly against GitHub, so anyone could pre-create a paper-titled discussion
 * before provisioning. We must never adopt a stranger's thread by title alone —
 * they could delete it and wipe the paper's comments. A title can also be
 * duplicated, so each title maps to a LIST and the caller picks a
 * maintainer-authored one (or warns).
 */
async function existingByTitle() {
  const out = new Map();
  let after = null;
  for (;;) {
    const data = await gql(
      `query($owner:String!,$name:String!,$after:String){
         repository(owner:$owner,name:$name){
           discussions(first:100, after:$after){
             pageInfo{ hasNextPage endCursor }
             nodes{ number title url author{ login } }
           }
         }
       }`,
      { owner, name, after },
    );
    const d = data.repository.discussions;
    for (const node of d.nodes) {
      const list = out.get(node.title) || [];
      list.push({
        number: node.number,
        url: node.url,
        author: node.author ? node.author.login : null,
      });
      out.set(node.title, list);
    }
    if (!d.pageInfo.hasNextPage) break;
    after = d.pageInfo.endCursor;
  }
  return out;
}

/** The login provisioning runs as — the maintainer whose threads we trust. */
async function viewerLogin() {
  const data = await gql(`query{ viewer{ login } }`, {});
  return data.viewer.login;
}

async function repoAndCategory() {
  const data = await gql(
    `query($owner:String!,$name:String!){
       repository(owner:$owner,name:$name){
         id
         discussionCategories(first:25){ nodes{ id name } }
       }
     }`,
    { owner, name },
  );
  const repoId = data.repository.id;
  const cat = (data.repository.discussionCategories.nodes || []).find(
    (c) => c.name === categoryName,
  );
  if (!cat) {
    throw new Error(
      `Discussions category "${categoryName}" not found — create it on the repo first.`,
    );
  }
  return { repoId, categoryId: cat.id };
}

async function createDiscussion(repoId, categoryId, paperId) {
  const data = await gql(
    `mutation($repositoryId:ID!,$categoryId:ID!,$title:String!,$body:String!){
       createDiscussion(input:{repositoryId:$repositoryId,categoryId:$categoryId,title:$title,body:$body}){
         discussion{ number }
       }
     }`,
    {
      repositoryId: repoId,
      categoryId,
      title: paperId,
      body: `Reader commentary for ${paperId}. Comments are posted from the paper page.`,
    },
  );
  return data.createDiscussion.discussion.number;
}

function loadMap() {
  try {
    const parsed = JSON.parse(readFileSync(mapPath, "utf8"));
    return parsed && typeof parsed === "object" ? parsed : {};
  } catch {
    return {};
  }
}

const paperIds = readdirSync(distPapers)
  .filter((n) => statSync(join(distPapers, n)).isDirectory())
  .sort();

const map = loadMap();
const missing = paperIds.filter((id) => typeof map[id] !== "number");
if (missing.length === 0) {
  console.log(`All ${paperIds.length} papers already provisioned. Nothing to do.`);
  process.exit(0);
}

console.log(`${paperIds.length} papers, ${missing.length} need a discussion.`);
const { repoId, categoryId } = await repoAndCategory();
const existing = await existingByTitle();
const maintainer = (await viewerLogin()).toLowerCase();
// The repo owner is also trusted (e.g. a thread created by the org account).
const trusted = new Set([maintainer, owner.toLowerCase()]);
const isTrusted = (author) => author !== null && trusted.has(author.toLowerCase());

let created = 0;
let reused = 0;
const skipped = [];
for (const paperId of missing) {
  const candidates = existing.get(paperId) || [];
  const mine = candidates.find((c) => isTrusted(c.author));
  if (mine) {
    // Adopt an existing thread ONLY when the maintainer (or repo owner) authored
    // it — never one a stranger squatted under the paper's title.
    map[paperId] = mine.number;
    reused++;
    console.log(`  reuse   ${paperId} → #${mine.number} (author @${mine.author})`);
  } else if (candidates.length > 0) {
    // A same-titled discussion exists but nobody trusted wrote it. Do NOT adopt
    // it and do NOT create a duplicate — an attacker squatting a title is a
    // signal to investigate, not something to auto-resolve.
    for (const c of candidates) {
      console.warn(
        `  SKIP    ${paperId}: foreign-authored discussion #${c.number} by @${c.author ?? "(deleted user)"} — ${c.url}`,
      );
    }
    skipped.push(paperId);
  } else {
    const number = await createDiscussion(repoId, categoryId, paperId);
    map[paperId] = number;
    created++;
    console.log(`  create  ${paperId} → #${number}`);
  }
}

const ordered = Object.fromEntries(Object.keys(map).sort().map((k) => [k, map[k]]));
writeFileSync(mapPath, `${JSON.stringify(ordered, null, 2)}\n`);
console.log(`Done: ${created} created, ${reused} reused, ${skipped.length} skipped. Wrote ${mapPath}.`);
console.log("Rebuild the site so the numbers are baked into the pages.");
if (skipped.length > 0) {
  console.error(
    `\n${skipped.length} paper(s) skipped because a foreign author already holds their title: ` +
      `${skipped.join(", ")}.\nThese stay UNPROVISIONED ("commenting isn't open") until you ` +
      `investigate. Delete the squatted discussion on github.com, then re-run.`,
  );
  process.exit(2);
}
