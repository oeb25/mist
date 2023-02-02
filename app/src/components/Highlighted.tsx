import React, { useEffect, useState } from "react";
import { MINT_ID } from "../lib/code/mint-language";
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
        .colorize(source || "", language || MINT_ID, {})
        .then(setHtml);
    }, [source, language]);

    return React.createElement("div", {
      id: "output",
      dangerouslySetInnerHTML: { __html: html },
    });
  };

  return { default: Highlighted };
});
