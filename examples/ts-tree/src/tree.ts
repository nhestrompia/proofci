// Values that hold values of their own type: a list, a tree and a JSON-like union.

export interface Item {
  value: number;
  next: Item | null;
}

export interface Tree {
  label: string;
  children: Tree[];
}

export type Json =
  | { kind: "num"; value: number }
  | { kind: "str"; value: string }
  | { kind: "list"; items: Json[] }
  | { kind: "pair"; left: Json; right: Json };

export function prepend(list: Item | null, value: number): Item {
  return { value, next: list };
}

export function total(list: Item | null): number {
  if (list === null) return 0;
  return list.value + total(list.next);
}

export function size(tree: Tree): number {
  return tree.children.map(child => size(child)).reduce((a, b) => a + b, 1);
}

export function hasLabel(tree: Tree, label: string): boolean {
  return tree.label === label || tree.children.some(child => hasLabel(child, label));
}

export function leaves(json: Json): number {
  switch (json.kind) {
    case "num":
    case "str":
      return 1;
    case "list":
      return json.items.reduce((n, item) => n + leaves(item), 0);
    case "pair":
      return leaves(json.left) + leaves(json.right);
  }
}
