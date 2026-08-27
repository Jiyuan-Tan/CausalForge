import { defineConfig } from "astro/config";
import sitemap from "@astrojs/sitemap";
import { readdir, access, cp } from "node:fs/promises";
import { join, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));

function bundleRoots() {
  const roots = [join(here, "..", "doc", "presentation")];
  if (process.env.SITE_FIXTURES === "1") roots.push(join(here, "fixtures"));
  return roots;
}

/** Copies each bundle's compiled paper.pdf into dist/papers/<id>/. */
function copyBundlePdfs() {
  return {
    name: "copy-bundle-pdfs",
    hooks: {
      "astro:build:done": async ({ dir }) => {
        const dist = fileURLToPath(dir);
        for (const root of bundleRoots()) {
          let names = [];
          try {
            names = await readdir(root);
          } catch {
            continue;
          }
          for (const name of names) {
            const pdf = join(root, name, "paper.pdf");
            const ok = await access(pdf).then(
              () => true,
              () => false,
            );
            if (ok) await cp(pdf, join(dist, "papers", name, "paper.pdf"));
          }
        }
      },
    },
  };
}

// GitHub Pages: set SITE_URL/SITE_BASE in the workflow when deploying under a
// project path (https://<org>.github.io/<repo>).
export default defineConfig({
  site: process.env.SITE_URL ?? "https://example.github.io",
  base: process.env.SITE_BASE ?? "/",
  output: "static",
  // Hover-prefetch every internal link: the paper page is ~1.5MB of build-time
  // KaTeX markup, so starting the fetch on hover makes paper↔slides jumps feel
  // instant instead of click-then-wait.
  prefetch: { prefetchAll: true, defaultStrategy: "hover" },
  // The sitemap is how search engines discover the library and paper pages —
  // nothing outside the site links to them. Data endpoints and the PDF routes
  // are not pages, so they stay out of it.
  integrations: [
    copyBundlePdfs(),
    sitemap({ filter: (page) => !/\.(json|pdf)$/.test(page) }),
  ],
  vite: {
    server: {
      // Build output and worker state are not site source, and watching them is
      // actively harmful here: both get created and removed under this
      // directory (a `wrangler deploy` writes `.wrangler/tmp`, a build writes
      // `dist*`), and on NFS a directory that vanishes mid-scan surfaces as a
      // stale handle (ESTALE) which Vite's watcher raises as an unhandled error
      // and dies on. Deploying the worker or running a build alongside the dev
      // server would otherwise kill it.
      watch: { ignored: ["**/.wrangler/**", "**/dist/**", "**/dist-*/**"] },
    },
  },
});
