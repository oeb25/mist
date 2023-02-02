@default:
    @just --choose

watch-sourcegen-ast:
    cargo watch --ignore generated.rs --clear -s "cargo test sourcegen_ast -- --nocapture; rustfmt src/generated.rs"

# UI

typeshare:
    typeshare . --lang=typescript --output-file=./app/src/lib/types.ts

build-wasm:
    cd app/wasm; wasm-pack build --release --target bundler

app: typeshare
    #!/bin/bash
    killall pueued
    trap 'kill $(jobs -p)' EXIT
    pueued &
    sleep 1
    pueue reset
    pueue parallel 2
    pueue add -w app -- npm run dev
    pueue add -w app/wasm 'watchexec -w ../.. -e rs "wasm-pack build --dev --target bundler"'
    sleep 1
    pueue follow 1

build-app: typeshare build-wasm
    cd app; npm install && npm run build

serve-app:
    miniserve --route-prefix mint --index index.html app/dist

SITE_ID := "43017e79-2762-45e6-9ba4-3bacedda3b96"

deploy-app: build-app
    cd app/dist; netlify deploy --prod -s {{SITE_ID}}
