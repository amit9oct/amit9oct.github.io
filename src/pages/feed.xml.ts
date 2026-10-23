import rss from '@astrojs/rss';
import type { APIContext } from 'astro';
import { site } from '../data/site';
import { getPosts } from '../lib/utils';

export async function GET(context: APIContext) {
  const posts = await getPosts();
  return rss({
    title: `Proof Sketches · ${site.name}`,
    description: site.description,
    site: context.site!,
    items: posts.map((p) => ({
      title: p.data.title,
      description: p.data.subtitle,
      pubDate: p.data.date,
      link: `/blog/${p.id}/`,
      categories: p.data.tags,
    })),
  });
}
