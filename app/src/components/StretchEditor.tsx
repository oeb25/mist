import { useEffect, useRef, useState } from "react";
import * as monaco from "monaco-editor";

import "monaco-editor/esm/vs/editor/editor.all.js";
import "monaco-editor/esm/vs/editor/standalone/browser/accessibilityHelp/accessibilityHelp.js";

import type { MarkerData } from "../lib/types";
import { MINT_ID } from "../lib/code/mint-language";
import { VITESSE_DARK } from "../lib/code/vitesse-theme";

export const StretchEditor = ({
  source,
  onChange,
  markers = [],
  language = MINT_ID,
}: {
  source: string;
  onChange?: (source: string) => void;
  markers?: MarkerData[];
  language?: string;
}) => {
  const [model] = useState(monaco.editor.createModel(source || "", language));

  const [container, setContainer] = useState<HTMLDivElement | null>(null);
  const editorRef = useRef<monaco.editor.IStandaloneCodeEditor | null>(null);

  useEffect(() => {
    if (container) {
      const editor = (editorRef.current = monaco.editor.create(container, {
        model,
        theme: VITESSE_DARK,
        minimap: { enabled: false },
        smoothScrolling: true,
        readOnly: !onChange,
        lineNumbers: "off",
        scrollBeyondLastLine: false,
        folding: false,
        quickSuggestions: false,
        language: language,
        wordWrap: "bounded",
        renderLineHighlightOnlyWhenFocus: true,
        scrollbar: {
          vertical: "auto",
          verticalScrollbarSize: 0,
        },
      }));

      updateMarkers(markers, editor);

      return () => {
        editor.dispose();
      };
    }
  }, [container]);

  useEffect(() => {
    const editor = editorRef.current;
    if (editor) editor.setModel(model);
  }, [model, editorRef.current]);

  useEffect(() => {
    const listener = () => {
      const editor = editorRef.current;
      if (editor) editor.layout();
    };

    if (editorRef.current) {
      editorRef.current.layout();
      editorRef.current.layout();
    }

    window.addEventListener("resize", listener);
    return () => window.removeEventListener("resize", listener);
  }, [editorRef.current]);

  useEffect(() => {
    const r = model.onDidChangeContent(
      () => onChange && onChange(model.getValue())
    );

    return () => r.dispose();
  }, [model, onChange]);

  useEffect(() => {
    if (source && model.getValue() != source) model.setValue(source);
  }, [onChange, source]);

  useEffect(() => {
    if (editorRef.current) updateMarkers(markers, editorRef.current);
  }, [markers]);

  return <div className="absolute inset-0" ref={setContainer} />;
};
function updateMarkers(
  markers: MarkerData[],
  editor: monaco.editor.IStandaloneCodeEditor
) {
  const markerDecs = markers.map<monaco.editor.IMarkerData>(
    ({ severity, relatedInformation, tags, ...m }) => {
      const res: monaco.editor.IMarkerData = {
        ...m,
        severity: monaco.MarkerSeverity[severity],
      };

      if (tags) res.tags = tags.map((t) => monaco.MarkerTag[t]);
      if (relatedInformation)
        res.relatedInformation =
          relatedInformation.map<monaco.editor.IRelatedInformation>((r) => ({
            resource: monaco.Uri.parse(r.resource),
            message: r.message,
            startLineNumber: r.startLineNumber,
            startColumn: r.startColumn,
            endLineNumber: r.endLineNumber,
            endColumn: r.endColumn,
          }));

      return res;
    }
  );

  monaco.editor.setModelMarkers(editor.getModel()!, "mint", markerDecs);
}
