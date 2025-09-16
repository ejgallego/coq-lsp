import * as vscode from "vscode";

interface GlowingSpan {
  range: vscode.Range;
  decoration: vscode.TextEditorDecorationType;
  timer?: any;
  startTime: number;
}

var activeSpan: GlowingSpan | null = null;

export function stop() {
  if (!activeSpan) return;

  let pulse = activeSpan;
  activeSpan = null;

  if (pulse.timer) clearInterval(pulse.timer); // clear interval or timeout
  pulse.decoration.dispose();
}

export function start(
  editor: vscode.TextEditor,
  range: vscode.Range,
  delayMs: number = 600
) {
  stop();

  // Initial invisible decoration
  const decoration = vscode.window.createTextEditorDecorationType({
    backgroundColor: `rgba(255,0,0,0)`,
  });
  editor.setDecorations(decoration, [range]);

  // Start pulsing after delay
  const timeout = setTimeout(() => {
    const startTime = Date.now();

    const timer = setInterval(() => {
      const elapsed = (Date.now() - startTime) / 1000; // seconds
      const baseIntensity = Math.min(elapsed * 0.2, 1); // grows over time
      const pulse = Math.sin(elapsed * 3) * 0.5 + 0.5; // oscillates 0..1
      const opacity = Math.min(baseIntensity * pulse, 1);

      const newDecoration = vscode.window.createTextEditorDecorationType({
        backgroundColor: `rgba(255,0,0,${opacity})`,
      });

      editor.setDecorations(newDecoration, [range]);

      // Dispose old decoration
      activeSpan?.decoration.dispose();

      // Update reference
      activeSpan = { range, decoration: newDecoration, timer, startTime };
    }, 200);

    // Save pulse info
    activeSpan = { range, decoration, timer, startTime };
  }, delayMs);

  // Temporarily store decoration so we can stop even during delay
  activeSpan = { range, decoration, startTime: Date.now(), timer: undefined };

  // Attach the timeout so it can be cleared if stopped before glow starts
  activeSpan.timer = timeout;
}
