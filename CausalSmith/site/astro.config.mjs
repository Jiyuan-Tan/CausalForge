import { defineConfig } from "astro/config";
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
  integrations: [copyBundlePdfs()],
});
