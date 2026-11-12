// From umami src/lib/types.ts, cut down to what `Auth` needs.
export interface Auth {
  user?: {
    id: string;
    username: string;
    role: string;
    isAdmin: boolean;
  };
  shareToken?: {
    websiteId?: string;
    linkId?: string;
    linkIds?: string[];
  };
}
