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
