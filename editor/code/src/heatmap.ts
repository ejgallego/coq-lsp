import {
  window,
  TextEditorDecorationType,
  Range,
  Disposable,
  TextEditor,
  languages,
  workspace,
  ConfigurationChangeEvent,
} from "vscode";

import { CoqSelector } from "./config";
import { DocumentPerfParams, SentencePerfParams } from "../lib/types";

export interface HeatMapConfig {
  enabled: boolean;
  heatLevels: number;
  warmColor: string;
  coldColor: string;
  perfDataType: "time" | "memory";
}

export class HeatMap {
  private enabled: boolean = false;
  private subscriptions: Disposable[] = [];
  private heatStyles: TextEditorDecorationType[] = [];
  private perfData: DocumentPerfParams<Range> | undefined = undefined;
  private perfDataType: "time" | "memory" = "time";

  constructor(config: HeatMapConfig) {
    this.enabled = config.enabled;
    this.apply_config(config);
    this.subscriptions.push(this.listenToConfigChanges());
  }

  dispose() {
    this.subscriptions.forEach((subscription) => subscription.dispose());
    this.heatStyles.forEach((style) => style.dispose());
  }

  toggle() {
    this.enabled = !this.enabled;
    if (this.enabled) {
      this.draw(window.activeTextEditor);
    } else {
      this.clearHeatMap();
    }
  }

  draw(editor?: TextEditor) {
    if (
      !editor ||
      !this.enabled ||
      languages.match(CoqSelector.local, editor.document) === 0 ||
      this.perfData === undefined
    ) {
      return;
    }

    const perfData = this.perfData;

    const getData = (perf: SentencePerfParams<Range>) => {
      if (this.perfDataType === "time") {
        return perf.info.time;
      } else if (this.perfDataType === "memory") {
        return perf.info.memory;
      } else {
        throw new Error("Unknown perfDataType");
      }
    };

    const dataPoints = perfData.timings.map(getData);
    const minData = Math.min(...dataPoints);
    const maxData = Math.max(...dataPoints);
    const dataRange = maxData - minData;

    if (dataRange === 0) {
      return;
    }

    const dataPerLevel = dataRange / this.heatStyles.length;
    const ranges: Range[][] = new Array(this.heatStyles.length)
      .fill(null)
      .map(() => []);

    this.perfData.timings.forEach((perf) => {
      const dataPoint = getData(perf);
      const bucket = Math.min(
        this.heatStyles.length - 1,
        Math.floor((dataPoint - minData) / dataPerLevel)
      );
      ranges[bucket].push(perf.range);
    });

    this.heatStyles.forEach((style, i) =>
      editor.setDecorations(style, ranges[i])
    );
  }

  private clearHeatMap() {
    const editor = window.activeTextEditor;
    if (editor) {
      this.heatStyles.forEach((style) => editor.setDecorations(style, []));
    }
  }

  private listenToConfigChanges() {
    return workspace.onDidChangeConfiguration(
      (event: ConfigurationChangeEvent) => {
        if (event.affectsConfiguration("coq-lsp.heatmap")) {
          let config = workspace
            .getConfiguration("coq-lsp")
            .get("heatmap") as HeatMapConfig;
          this.apply_config(config);
          this.draw(window.activeTextEditor);
        }
      }
    );
  }

  private apply_config(config: HeatMapConfig) {
    // Read settings
    const heatLevels = config.heatLevels || 100;
    const warmColor = config.warmColor || "#ff0000";
    const coldColor = config.coldColor || "#000000";
    this.perfDataType = config.perfDataType || "time";

    // Use the settings
    this.updateHeatMapStyles(heatLevels, warmColor, coldColor);
  }

  private updateHeatMapStyles(
    heatLevels: number,
    warmColour: string,
    coldColour: string
  ) {
    this.heatStyles.forEach((style) => style.dispose()); // Clear existing styles
    this.heatStyles = [];

    const [r1, g1, b1] = this.parseColor(coldColour);
    const [r2, g2, b2] = this.parseColor(warmColour);

    for (let i = 0; i < heatLevels; i++) {
      const alphaValue = i / (heatLevels - 1);
      const r = Math.round(r1 + (r2 - r1) * alphaValue);
      const g = Math.round(g1 + (g2 - g1) * alphaValue);
      const b = Math.round(b1 + (b2 - b1) * alphaValue);

      this.heatStyles.push(
        window.createTextEditorDecorationType({
          backgroundColor: `rgba(${r}, ${g}, ${b}, ${alphaValue})`,
        })
      );
    }
  }

  // Parse hexadecimal color
  private parseColor(color: string): number[] {
    const hexRegex = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i;
    const matches = color.match(hexRegex);
    if (!matches) {
      console.warn(
        `Invalid color format: ${color}. Using default color "#ff0000."`
      );
      return [0xff, 0, 0]; // Default to red
    }
    return [
      parseInt(matches[1], 16),
      parseInt(matches[2], 16),
      parseInt(matches[3], 16),
    ];
  }

  update(data: DocumentPerfParams<Range>) {
    this.perfData = data;
    this.draw(window.activeTextEditor);
  }
}
