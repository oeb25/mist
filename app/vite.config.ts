import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";
import crossOriginIsolated from "vite-plugin-cross-origin-isolation";

// https://vitejs.dev/config/
export default defineConfig({
  base: "mint",
  plugins: [react(), crossOriginIsolated()],
});
