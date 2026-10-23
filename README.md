# iamthakur.com

Personal site of Amitayush Thakur, built with [Astro](https://astro.build) and deployed to GitHub Pages by
`.github/workflows/deploy.yml` on every push to `master`.

## Everyday edits

| To change… | Edit |
|---|---|
| Bio, links, job-market banner | `src/data/site.ts`, `src/pages/index.astro` |
| Papers | `src/data/papers.ts` (set `selected: true` to show on the home page) |
| News, experience, talks | `src/data/news.ts` |
| CV | replace `public/cv.pdf` |
| Blog posts | add `src/content/blog/<slug>.md` (or `.mdx`) |

## Writing a post

```md
---
title: My post
subtitle: One-line hook
date: 2026-11-01
tags: [Theorem Proving, Lean]
thumbnail: /assets/img/my-post/thumbnail.png   # also used as the social preview image
paper: https://arxiv.org/abs/...                # optional buttons
code: https://github.com/...
draft: true                                     # visible in `npm run dev` only
---
```

- Math: `$inline$` and `$$display$$` (KaTeX).
- Code: fenced blocks with `lean`, `coq`, `python`, and so on.
- Callouts: `:::definition[Title]`, `:::theorem`, `:::lemma`, `:::problem`, `:::remark`, `:::note`, `:::example`, closed with `:::`.
- An image followed directly by a `>` quote renders the quote as a figure caption.
- Comments (Giscus, stored as GitHub Discussions) are on by default; set `comments: false` to turn them off for a post.
- Images go in `public/assets/img/<post>/` and are referenced as `/assets/img/<post>/file.png`.

## Local development

```sh
npm install
npm run dev      # http://localhost:4321
npm run build    # outputs to dist/
```

The pre-2023 posts are kept, unpublished, in `_old_posts/`.
