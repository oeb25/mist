/// <reference types="astro/client" />

declare module "z3-solver/build/z3-built" {
  export default function (opts: {
    locateFile: (f: string) => f;
    mainScriptUrlOrBlob: string;
  }): any;
}
