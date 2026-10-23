import { defineConfig } from 'astro/config';
import mdx from '@astrojs/mdx';
import { unified } from '@astrojs/markdown-remark';
import sitemap from '@astrojs/sitemap';
import remarkMath from 'remark-math';
import remarkDirective from 'remark-directive';
import rehypeKatex from 'rehype-katex';
import { remarkCallouts } from './src/plugins/remark-callouts.mjs';

export default defineConfig({
  site: 'https://iamthakur.com',
  integrations: [mdx(), sitemap()],
  markdown: {
    processor: unified({
      remarkPlugins: [remarkMath, remarkDirective, remarkCallouts],
      rehypePlugins: [rehypeKatex],
    }),
    shikiConfig: {
      themes: { light: 'github-light', dark: 'github-dark-dimmed' },
      langAlias: { lean3: 'lean' },
    },
  },
  // Keep old Jekyll URLs alive (the COPRA paper links to the blog post).
  redirects: {
    '/2023-10-09-AutomaticTheoremProvingAndLanguageAgents': '/blog/copra',
    '/aboutme': '/',
    '/resume': '/cv',
    '/tags': '/blog',
  },
});
