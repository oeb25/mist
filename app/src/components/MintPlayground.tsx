import React, { useState } from "react";
import type { ParseResult } from "../lib/types";

export const MintPlayground = React.lazy(async () => {
  const [
    { StretchEditor },
    { Highlighted },
    { SYNTAX_TREE_ID },
    { init_hooks, parse },
  ] = await Promise.all([
    import("./StretchEditor"),
    import("./Highlighted"),
    import("../lib/code/syntax-tree-language"),
    import("mint-wasm"),
  ]);

  init_hooks();

  const MintPlayground = ({ src: initialSrc = SAMPLE }: { src?: string }) => {
    const [src, setSrc] = useState(initialSrc);

    const parseResult: ParseResult = JSON.parse(parse(src));

    return (
      <div className="not-prose grid h-64 grid-cols-2 shadow-lg md:-mx-14 lg:-mx-36 lg:grid-cols-[7fr_5fr]">
        <div className="relative grid rounded-l-lg bg-[#121212] py-2">
          <div className="relative">
            <StretchEditor
              source={src}
              onChange={setSrc}
              markers={parseResult.markers}
            />
          </div>
        </div>
        <div className="overflow-scroll rounded-r-lg bg-stone-900 p-2 text-xs text-white">
          <Highlighted
            source={parseResult.parseTree}
            language={SYNTAX_TREE_ID}
          />
        </div>
      </div>
    );
  };

  return { default: MintPlayground };
});

const SAMPLE = `
const y = 12;

fn hello(x: Int) {
    assume false;
    assert true;
}

// and a comment here
fn world() {
    // comment here
    let x = y + (z + 3 * 4);
    hello(x, true);
}
`.trim();
