import { Mutex } from "async-mutex";
import { init } from "z3-solver/build/low-level";
import initZ3 from "z3-solver/build/z3-built";

type Z3Instance = Awaited<ReturnType<typeof init>>;

const lock = new Mutex();
let stored = init(
  async () =>
    await initZ3({
      locateFile: (f) => f,
      mainScriptUrlOrBlob: "z3-built.js",
    })
);
const borrow = async <T>(f: (x: Z3Instance) => Promise<T>): Promise<T> => {
  const release = await lock.acquire();
  return f(await stored).finally(release);
};

export const run = async (query: string, onStart?: () => void) =>
  borrow(async ({ Z3 }) => {
    onStart?.();

    const cfg = Z3.mk_config();
    const ctx = Z3.mk_context(cfg);
    Z3.del_config(cfg);

    const results: string[] = [];

    for (const l of query.split("\n")) {
      const res = await Z3.eval_smtlib2_string(ctx, l);
      results.push(res);
    }

    Z3.del_context(ctx);

    return results;
  });
