import { defineConfig } from "astro/config";

import compress from "astro-compress";
import mdx from "@astrojs/mdx";
import react from "@astrojs/react";
import tailwind from "@astrojs/tailwind";
import wasm from "vite-plugin-wasm";

// https://astro.build/config
export default defineConfig({
  integrations: [compress(), mdx(), react(), tailwind()],
  site: "https://oeb25.github.io",
  vite: {
    plugins: [wasm()],
  },
  markdown: {
    drafts: true,
    shikiConfig: {
      theme: "vitesse-dark",
    },
  },
});
