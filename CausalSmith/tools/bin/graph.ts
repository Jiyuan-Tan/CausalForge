#!/usr/bin/env -S node --import tsx
import { runCli } from "../src/graph/cli.js";

runCli(process.argv.slice(2)).then((code) => process.exit(code));
