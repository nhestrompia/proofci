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

// A type that contains itself: a function reads the first level, and deeper values are opaque.
export interface Entry {
  name: string;
  parent: Entry | null;
  children: Entry[];
}

// An options object with nothing in it (or only members a function never reads)
export interface SendOptions {}
