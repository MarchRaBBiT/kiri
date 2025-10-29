export type SimpleYamlValue =
  | string
  | number
  | boolean
  | null
  | SimpleYamlValue[]
  | Record<string, SimpleYamlValue>;

function parseScalar(value: string): SimpleYamlValue {
  let trimmed = value.trim();
  const commentIndex = trimmed.indexOf(" #");
  if (commentIndex >= 0) {
    trimmed = trimmed.slice(0, commentIndex).trim();
  }
  if (trimmed === "true") return true;
  if (trimmed === "false") return false;
  if (trimmed === "null") return null;
  if (/^-?\d+(\.\d+)?$/.test(trimmed)) {
    return Number(trimmed);
  }
  if (trimmed.startsWith('"') && trimmed.endsWith('"')) {
    return trimmed.slice(1, -1);
  }
  if (trimmed.startsWith("'") && trimmed.endsWith("'")) {
    return trimmed.slice(1, -1);
  }
  return trimmed;
}

interface StackEntry {
  indent: number;
  value: SimpleYamlValue;
}

function ensureObject(value: SimpleYamlValue): Record<string, SimpleYamlValue> {
  if (!value || typeof value !== "object" || Array.isArray(value)) {
    throw new Error("Expected mapping");
  }
  return value as Record<string, SimpleYamlValue>;
}

export function parseSimpleYaml(content: string): Record<string, SimpleYamlValue> {
  const root: Record<string, SimpleYamlValue> = {};
  const lines = content.split(/\r?\n/);
  const stack: StackEntry[] = [{ indent: -1, value: root }];

  for (let index = 0; index < lines.length; index++) {
    const rawLine = lines[index];
    if (/^\s*$/.test(rawLine) || /^\s*#/.test(rawLine)) {
      continue;
    }
    const indent = rawLine.match(/^\s*/)?.[0].length ?? 0;
    const line = rawLine.trim();

    while (stack.length > 0 && indent <= stack[stack.length - 1].indent) {
      stack.pop();
    }
    const parent = stack[stack.length - 1];
    const container = parent.value;

    if (line.startsWith("- ")) {
      if (!Array.isArray(container)) {
        throw new Error("List item without array context");
      }
      (container as SimpleYamlValue[]).push(parseScalar(line.slice(2)));
      continue;
    }

    const separatorIndex = line.indexOf(":");
    if (separatorIndex === -1) {
      throw new Error(`Invalid YAML line: ${line}`);
    }
    const key = line.slice(0, separatorIndex).trim();
    const remainder = line.slice(separatorIndex + 1);
    const target = ensureObject(container);
    if (remainder.trim().length === 0) {
      const nextLine = lines[index + 1];
      const isList = nextLine ? nextLine.trim().startsWith("- ") : false;
      if (isList) {
        const arr: SimpleYamlValue[] = [];
        target[key] = arr;
        stack.push({ indent, value: arr });
      } else {
        const obj: Record<string, SimpleYamlValue> = {};
        target[key] = obj;
        stack.push({ indent, value: obj });
      }
    } else {
      target[key] = parseScalar(remainder);
    }
  }

  return root;
}
