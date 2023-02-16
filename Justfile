@default:
    @just --choose

watch-sourcegen-ast:
    cargo watch --ignore generated.* --clear -s "cargo test sourcegen_ast -- --nocapture; rustfmt src/generated.rs"

# UI

app-typeshare:
    typeshare . --lang=typescript --output-file=./app/src/lib/types.ts

app-build-wasm:
    cd app/wasm; wasm-pack build --release --target bundler

app: app-typeshare
    tmuxinator

app-tmux-astro:
    cd app; npm run dev
app-tmux-wasm:
    cd app/wasm/; watchexec -w ../.. -e rs "wasm-pack build --dev --target bundler"

app-build: app-typeshare app-build-wasm
    cd app; npm install && npm run build

app-serve:
    miniserve --index index.html app/dist

SITE_ID := "43017e79-2762-45e6-9ba4-3bacedda3b96"

app-deploy: app-build
    cd app/dist; netlify deploy --prod -s {{SITE_ID}}
