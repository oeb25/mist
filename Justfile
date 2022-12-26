@default:
    @just --choose

app:
    cd app; npm run dev

build-app:
    cd app; npm install && npm run build
