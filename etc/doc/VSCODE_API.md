# Welcome to the developer documentation for the coq-lsp VSCode extension

As of today, the extension provides two extensions for other
developers to use:

```typescript
export interface CoqLspAPI {
  /**
   * Query goals from Coq
   */
  goalsRequest(params: GoalRequest): Promise<GoalAnswer<PpString>>;

  /**
   * Register callback action on user-initiated goals request
   */
  onUserGoals(fn: (goals: GoalAnswer<String>) => void): Disposable;
}
```

Types are for now in the `lib/types.ts` file, we would be happy to
provide a separate package soon.

## Querying goals from Coq:

Use `goalsRequest` to perform your own queries to Coq, and handle the
answer in your own extension.

## Reacting to user demands for Goals:

Alternatively, you can instead have `coq-lsp` call your code when the
user request the goals. In order to register the callback, you can use
the `onUserGoals` API function.

Don't forget to dispose of your callback when your extension is
de-activated.
