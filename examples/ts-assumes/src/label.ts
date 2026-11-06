import { slug } from "slug-maker";

export function label(title: string): string {
  return `#${slug(title)}`;
}
