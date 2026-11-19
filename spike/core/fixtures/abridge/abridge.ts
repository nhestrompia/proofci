import { getCount, getName, logEvent } from "./world";

export async function greet(id: string): Promise<string> {
  const n = await getName(id);
  if (n === "") {
    return "anon";
  }
  return "hi " + n;
}

export async function safeName(id: string): Promise<string> {
  try {
    const n = await getName(id);
    return n;
  } catch (e) {
    if (e instanceof Error) {
      return "failed: " + e.message;
    }
    throw e;
  }
}

