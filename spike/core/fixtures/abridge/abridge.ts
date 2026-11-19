import { getCount, getName, logEvent, setScore } from "./world";

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


export async function logged(id: string): Promise<number> {
  await logEvent(id);
  const c = await getCount(id);
  return c + 1;
}

export async function nameOf(id: string): Promise<string> {
  return await getName(id);
}

export async function scoreBoth(id: string, other: string): Promise<boolean> {
  const a = await setScore(id, 1);
  if (!a) {
    throw new Error("first failed");
  }
  return await setScore(other, 2);
}

export async function countOrZero(id: string): Promise<number> {
  try {
    return await getCount(id);
  } catch (e) {
    return 0;
  }
}
