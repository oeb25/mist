import { defineConfig } from "astro/config";

// https://astro.build/config
import compress from "astro-compress";
import mdx from "@astrojs/mdx";
import react from "@astrojs/react";
import tailwind from "@astrojs/tailwind";

// https://astro.build/config
export default defineConfig({
  integrations: [compress(), mdx(), react(), tailwind()],
  site: "https://oeb25.github.io",
  base: "/mint",
});
