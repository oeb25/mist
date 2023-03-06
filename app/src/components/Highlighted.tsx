import React, { useEffect, useState } from "react";
import { MIST_ID } from "../lib/code/mist-language";
import { VITESSE_DARK } from "../lib/code/vitesse-theme";

export const Highlighted = React.lazy(async () => {
  const monaco = await import("monaco-editor");

  const Highlighted = ({
    source,
    language,
  }: {
    source: string;
    language: string;
  }) => {
    const [html, setHtml] = useState("");

    useEffect(() => {
      monaco.editor.setTheme(VITESSE_DARK);
      monaco.editor
        .colorize(source || "", language || MIST_ID, {})
        .then(setHtml);
    }, [source, language]);

    return React.createElement("div", {
      id: "output",
      style: { fontFamily: 'Menlo, Monaco, "Courier New", monospace' },
      dangerouslySetInnerHTML: { __html: html },
    });
  };

  return { default: Highlighted };
});
