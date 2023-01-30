import { useEffect, useState } from "react";
import { run } from "../lib/z3";

const query = `
(declare-const x Int)
(assert (= x 12))
(check-sat)
(get-model)
`.trim();

run(query);

export const Z3Playground = () => {
  const [code, setCode] = useState(query);
  const [result, setResult] = useState<string[]>([]);
  const [status, setStatus] = useState<"evaluating" | { doneIn: number }>(
    "evaluating"
  );

  useEffect(() => {
    let start = window.performance.now();
    run(code, () => {
      start = window.performance.now();
      setStatus("evaluating");
    }).then((r) => {
      setResult(r);
      setStatus({ doneIn: window.performance.now() - start });
    });
  }, [code, setResult]);

  return (
    <div className="grid min-h-screen grid-rows-[auto_1fr] gap-5">
      <div className="mt-10 px-10">
        <h1 className="text-2xl text-slate-700">Run Z3 with WASM</h1>
        <p>
          This is a demo page for interacting with Z3 in the browser through
          WASM
        </p>
      </div>
      <div className="grid grid-cols-2 gap-10 p-10">
        <div className="grid resize-none grid-rows-[auto_1fr] rounded-xl border p-4 shadow-xl">
          <div className="-mx-1 mb-4 border-b px-1 pb-2">
            <h2 className="text-xl">Input</h2>
          </div>
          <textarea
            className="resize-none  font-mono"
            value={code}
            onChange={(e) => setCode(e.target.value)}
          />
        </div>
        <div className="grid resize-none grid-rows-[auto_1fr] rounded-xl border bg-slate-50 p-4 shadow-xl">
          <div className="-mx-1 mb-4 flex justify-between border-b px-1 pb-2">
            <h2 className="text-xl">Output</h2>
            <div className="text-slate-400">
              {status == "evaluating"
                ? "Evaluating..."
                : `Evaluated in ${status.doneIn.toFixed(2)}ms`}
            </div>
          </div>
          <pre className="italic text-slate-800">
            {result
              .map((l) => l.trim())
              .filter((l) => l.trim())
              .join("\n")}
          </pre>
        </div>
      </div>
    </div>
  );
};
