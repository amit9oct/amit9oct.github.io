import { getCollection, type CollectionEntry } from 'astro:content';

export const formatDate = (d: Date) =>
  d.toLocaleDateString('en-US', { year: 'numeric', month: 'short', day: 'numeric', timeZone: 'UTC' });

export const tagSlug = (tag: string) =>
  tag.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/(^-|-$)/g, '');

export const readingTime = (body = '') => {
  const words = body.replace(/```[\s\S]*?```/g, '').split(/\s+/).filter(Boolean).length;
  return Math.max(1, Math.round(words / 230));
};

/** The post's `thumbnail`, or else the first image in its body. */
export const postImage = (post: CollectionEntry<'blog'>) =>
  post.data.thumbnail ?? post.body?.match(/!\[[^\]]*\]\(([^)\s]+)/)?.[1];

/** Published posts, newest first. Drafts show up in `npm run dev` only. */
export async function getPosts() {
  const posts = await getCollection('blog', ({ data }) => import.meta.env.DEV || !data.draft);
  return posts.sort((a, b) => b.data.date.valueOf() - a.data.date.valueOf());
}
