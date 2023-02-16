import React, { useEffect, useMemo, useState } from "react";
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

  const MintPlayground = ({
    src: initialSrc = SAMPLE,
    large = false,
  }: {
    src?: string;
    large?: boolean;
  }) => {
    const [src, setSrc] = useState(initialSrc);

    const parseResult: ParseResult = useMemo(
      () => JSON.parse(parse(src)),
      [src]
    );

    const parseTree = useDebounce(parseResult.parseTree, 100);

    return (
      <div
        className={
          "not-prose grid grid-cols-2 shadow-lg md:-mx-14 lg:-mx-36 lg:grid-cols-[7fr_5fr] " +
          (large ? "h-96" : "h-64")
        }
      >
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
          <Highlighted source={parseTree} language={SYNTAX_TREE_ID} />
        </div>
      </div>
    );
  };

  return { default: MintPlayground };
});

function useDebounce<T>(value: T, durationMs: number): T {
  const [stored, setStored] = useState(value);

  useEffect(() => {
    const t = setTimeout(() => setStored(value), durationMs);
    return () => clearTimeout(t);
  }, [value, durationMs]);

  return stored;
}

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

export const SAMPLES = {
  euclid: `
pure fn gcd(x: Int, y: Int) -> Int
  requires x > 0, y > 0
  ensures
      result >= 1,
      divides(result, x),
      divides(result, y),
      forall(z: Int) if z >= 1 && divides(z, x) && divides(z, y) {
        z <= result
      };


macro divides_prop(x, y, z) { z >= 0 && x * z == y }

pure fn divides(x: Int, y: Int) -> Bool
  requires x > 0, y > 0
  ensures  result == exists(z: Int) divides_prop(x, y, z);


ghost fn lemma_show_divides(x: Int, y: Int, z: Int)
  requires x > 0, y > 0,
           divides_prop(x, y, z)
  ensures  divides(x, y);

ghost fn lemma_divides(x: Int, y: Int)
  requires x > 0, y > 0
  ensures  gcd(x + y, y) == gcd(x, y)
{
  lemma_gcd_lower(x, y);
  lemma_gcd_lower(x, y);
}

ghost fn lemma_gcd_upper(x: Int, y: Int)
  requires x > 0, y > 0
  ensures gcd(x + y, y) >= gcd(x, y)
{
  let z = x + y;
  let m = gcd(x + y, y);
  let n = gcd(y, x);

  let c = lemma_divides(n, y);
  let d = lemma_divides(n, x);

  lemma_show_divides(n, x + y, c + d);
}

ghost fn lemma_gcd_lower(x: Int, y: Int)
  requires x > 0, y > 0
  ensures gcd(x + y, y) <= gcd(x, y)
{
  let z = x + y;
  let m = gcd(x + y, y);

  let c = lemma_divides(m, z);
  let d = lemma_divides(m, y);

  lemma_show_divides(m, x, c - d);
}

ghost fn lemma_gcd_idempotent(x: Int)
  requires x > 0
  ensures gcd(x, x) == x
{
  lemma_show_divides(x, x, 1);
}

macro V(x, y) { x + y }

fn euclid(n: Int, m: Int) -> Int
  requires n > 0, m > 0
  ensures result == gcd(n, m)
{
  let a = m;
  let b = m;
  while a != b
      invariant a > 0, b > 0,
                gcd(a, b) == gcd(n, m)
  {
      if a > b {
          a = a - b;
          lemma_gcd(a, b);
      } else {
          b = b - a;
          lemma_gcd(b, a);
      }
  }

  assert a == b, gcd(a, b) == gcd(n, m);
  lemma_gcd_idempotent(a);
  assert gcd(n, m) == a;

  return a;
}
`.trimStart(),
};
