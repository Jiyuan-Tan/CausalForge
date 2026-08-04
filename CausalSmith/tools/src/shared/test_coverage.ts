import ts from "typescript";

/** Count executable Vitest cases in a test source file using the TypeScript AST,
 * so text inside comments, strings, or template literals never counts. A case is
 * a call whose root callee is `it` or `test`, through any modifier chain
 * (`.only`, `.fails`, `.concurrent`, `.each(...)` counted once at the outer
 * call). `.skip` and `.todo` are EXCLUDED on purpose — including every test
 * inside a `describe.skip`/`describe.todo` block: converting live tests to
 * skipped ones is a coverage loss and must trip the baseline check. */
export function countTestCases(source: string, fileName = "file.test.ts"): number {
  const sf = ts.createSourceFile(fileName, source, ts.ScriptTarget.Latest, true);
  let count = 0;
  const unwrap = (expr: ts.Expression): { root: string; mods: string[] } | null => {
    const mods: string[] = [];
    let cur: ts.Expression = expr;
    while (true) {
      if (ts.isPropertyAccessExpression(cur)) {
        mods.push(cur.name.text);
        cur = cur.expression;
      } else if (ts.isCallExpression(cur)) {
        cur = cur.expression;
      } else break;
    }
    return ts.isIdentifier(cur) ? { root: cur.text, mods } : null;
  };
  const visit = (node: ts.Node, inSkippedSuite: boolean): void => {
    let skipped = inSkippedSuite;
    if (
      ts.isCallExpression(node) &&
      // Skip the inner call of an `it.each(table)(...)` chain; only the outer
      // call that actually registers the case is counted.
      !(ts.isCallExpression(node.parent) && node.parent.expression === node)
    ) {
      const info = unwrap(node.expression);
      const parked = info !== null && (info.mods.includes("skip") || info.mods.includes("todo"));
      if (info?.root === "describe" && parked) skipped = true;
      if (
        info !== null &&
        (info.root === "it" || info.root === "test") &&
        !parked && !skipped
      ) count += 1;
    }
    ts.forEachChild(node, (child) => visit(child, skipped));
  };
  visit(sf, false);
  return count;
}
