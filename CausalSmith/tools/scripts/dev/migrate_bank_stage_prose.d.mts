export interface MigrationResult {
  content: string;
  substitutions: number;
}

export interface MigrationSummary {
  filesScanned: number;
  filesTouched: number;
  totalSubstitutions: number;
  changed: Array<{
    file: string;
    substitutions: number;
  }>;
}

export function migrateMarkdown(content: string): MigrationResult;

export function runMigration(options?: {
  repoRoot?: string;
  write?: boolean;
}): Promise<MigrationSummary>;
