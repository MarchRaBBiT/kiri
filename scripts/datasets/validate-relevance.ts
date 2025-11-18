#!/usr/bin/env tsx
/**
 * Validate relevance scores in dataset expected sections
 *
 * Checks:
 * 1. relevance is within 0-3 range
 * 2. Each query has at least one relevance > 0
 * 3. path is a string
 * 4. expected is an array
 */

import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import * as yaml from "yaml";

interface ExpectedItem {
  path: string;
  relevance: number;
}

interface QueryMetadata {
  expected?: (string | ExpectedItem)[];
  [key: string]: unknown;
}

interface Query {
  id: string;
  metadata?: QueryMetadata;
}

interface Dataset {
  queries: Query[];
}

interface ValidationError {
  queryId: string;
  field: string;
  message: string;
}

function validateDataset(datasetPath: string): ValidationError[] {
  const errors: ValidationError[] = [];

  const content = readFileSync(datasetPath, "utf-8");
  const dataset = yaml.parse(content) as Dataset;

  if (!dataset.queries || !Array.isArray(dataset.queries)) {
    errors.push({
      queryId: "root",
      field: "queries",
      message: "Dataset must have a queries array",
    });
    return errors;
  }

  for (const query of dataset.queries) {
    const expected = query.metadata?.expected;

    // Check if expected is an array
    if (expected !== undefined && !Array.isArray(expected)) {
      errors.push({
        queryId: query.id,
        field: "expected",
        message: "expected must be an array",
      });
      continue;
    }

    if (!expected || expected.length === 0) {
      // No expected items - this might be valid for some queries
      continue;
    }

    let hasRelevantItem = false;

    for (let i = 0; i < expected.length; i++) {
      const item = expected[i];

      if (typeof item === "string") {
        // Old format - string path (treated as relevance=1)
        hasRelevantItem = true;
        continue;
      }

      if (typeof item !== "object" || item === null) {
        errors.push({
          queryId: query.id,
          field: `expected[${i}]`,
          message: "expected item must be a string or object",
        });
        continue;
      }

      const expectedItem = item as ExpectedItem;

      // Check path is a string
      if (typeof expectedItem.path !== "string") {
        errors.push({
          queryId: query.id,
          field: `expected[${i}].path`,
          message: "path must be a string",
        });
      }

      // Check relevance exists and is a number
      if (typeof expectedItem.relevance !== "number") {
        errors.push({
          queryId: query.id,
          field: `expected[${i}].relevance`,
          message: "relevance must be a number",
        });
        continue;
      }

      // Check relevance is within 0-3 range
      if (expectedItem.relevance < 0 || expectedItem.relevance > 3) {
        errors.push({
          queryId: query.id,
          field: `expected[${i}].relevance`,
          message: `relevance must be between 0 and 3, got ${expectedItem.relevance}`,
        });
      }

      if (expectedItem.relevance > 0) {
        hasRelevantItem = true;
      }
    }

    // Check each query has at least one relevant item
    if (!hasRelevantItem) {
      errors.push({
        queryId: query.id,
        field: "expected",
        message: "query must have at least one item with relevance > 0",
      });
    }
  }

  return errors;
}

function main(): void {
  const args = process.argv.slice(2);

  if (args.length === 0) {
    console.error("Usage: validate-relevance.ts <dataset-path>");
    process.exit(1);
  }

  const firstArg = args[0];
  if (!firstArg) {
    console.error("Usage: validate-relevance.ts <dataset-path>");
    process.exit(1);
  }

  const datasetPath = resolve(firstArg);
  console.log(`📖 Validating dataset: ${datasetPath}`);

  try {
    const errors = validateDataset(datasetPath);

    if (errors.length === 0) {
      console.log("✅ Dataset validation passed!");
      console.log("   All relevance scores are valid.");
      process.exit(0);
    } else {
      console.log(`❌ Dataset validation failed with ${errors.length} error(s):\n`);

      for (const error of errors) {
        console.log(`   Query: ${error.queryId}`);
        console.log(`   Field: ${error.field}`);
        console.log(`   Error: ${error.message}`);
        console.log();
      }

      process.exit(1);
    }
  } catch (error) {
    console.error(`❌ Failed to validate dataset: ${error}`);
    process.exit(1);
  }
}

main();
