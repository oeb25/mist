import React, { useEffect, useMemo, useState } from "react";
import type { ParseResult } from "../lib/types";

export const MistPlayground = React.lazy(async () => {
  const [
    { StretchEditor },
    { Highlighted },
    { SYNTAX_TREE_ID },
    { init_hooks, parse },
  ] = await Promise.all([
    import("./StretchEditor"),
    import("./Highlighted"),
    import("../lib/code/syntax-tree-language"),
    import("mist-wasm"),
  ]);

  init_hooks();

  const MistPlayground = ({
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

  return { default: MistPlayground };
});

export const MistTypeCheck = React.lazy(async () => {
  const [
    { StretchEditor },
    { Highlighted },
    { VIPER_ID },
    { init_hooks, type_check },
  ] = await Promise.all([
    import("./StretchEditor"),
    import("./Highlighted"),
    import("../lib/code/viper-language"),
    import("mist-wasm"),
  ]);

  init_hooks();

  const MistTypeCheck = ({
    src: initialSrc = SAMPLE,
    large = false,
  }: {
    src?: string;
    large?: boolean;
  }) => {
    const [src, setSrc] = useState(initialSrc);

    const parseResult: ParseResult = useMemo(() => {
      try {
        return JSON.parse(type_check(src));
      } catch (e) {
        console.error(e);
        return { parseTree: "", markers: [] };
      }
    }, [src]);

    const parseTree = useDebounce(parseResult.parseTree, 100);

    return (
      <div
        className={
          "not-prose grid grid-cols-2 shadow-lg md:-mx-14 lg:-mx-36 " +
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
          <Highlighted source={parseTree} language={VIPER_ID} />
        </div>
      </div>
    );
  };

  return { default: MistTypeCheck };
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

fn hello(x: int) {
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
  pure fn gcd(x: int, y: int) -> int
  requires x > 0, y > 0
  ensures
    result >= 1,
    divides(result, x),
    divides(result, y),
    forall(z: int) if z >= 1 && divides(z, x) && divides(z, y) {
      z <= result
    };


macro divides_prop(x, y, z) { z >= 0 && x * z == y }

pure fn divides(x: int, y: int) -> bool
  requires x > 0, y > 0
  ensures  result == exists(z: int) divides_prop(x, y, z);


ghost fn lemma_show_divides(x: int, y: int, z: int)
  requires x > 0, y > 0,
           divides_prop(x, y, z)
  ensures  divides(x, y);

ghost fn lemma_divides(x: int, y: int) -> int
  requires x > 0, y > 0
  requires divides(x, y)
  ensures divides_prop(x, y, result)

ghost fn lemma_gcd(x: int, y: int)
  requires x > 0, y > 0
  ensures gcd(x + y, y) == gcd(x, y)
{
  lemma_gcd_lower(x, y)
  lemma_gcd_upper(x, y)
}

ghost fn lemma_gcd_upper(x: int, y: int)
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

ghost fn lemma_gcd_lower(x: int, y: int)
  requires x > 0, y > 0
  ensures gcd(x + y, y) <= gcd(x, y)
{
  let z = x + y;
  let m = gcd(x + y, y);

  let c = lemma_divides(m, z);
  let d = lemma_divides(m, y);

  lemma_show_divides(m, x, c - d);
}

ghost fn lemma_gcd_idempotent(x: int)
  requires x > 0
  ensures gcd(x, x) == x
{
  lemma_show_divides(x, x, 1);
}

macro V(x, y) { x + y }

fn euclid(n: int, m: int) -> int
  requires n > 0, m > 0
  ensures result == gcd(n, m)
{
  let a = n;
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
