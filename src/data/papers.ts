export type Theme = 'agents' | 'verified-code' | 'neurosymbolic' | 'other';

export type Paper = {
  title: string;
  authors: string; // ME is highlighted automatically
  venue: string;
  year: number;
  theme: Theme;
  award?: string;
  thumbnail?: string;
  selected?: boolean;
  links: { label: string; href: string }[];
};

export const ME = 'Amitayush Thakur';

export const themes: Record<Theme, { title: string; blurb: string }> = {
  agents: {
    title: 'Theorem-proving agents',
    blurb: 'LLM agents, benchmarks, and data pipelines for writing machine-checked proofs in Lean, Coq, and Isabelle.',
  },
  'verified-code': {
    title: 'Verified code generation',
    blurb: 'Generating programs together with formal specifications and proofs that they are correct.',
  },
  neurosymbolic: {
    title: 'Neuro-symbolic AI',
    blurb: 'Pairing LLMs with symbolic structure: programming languages that agents think and act in, and systems that discover mathematics by inventing concepts and judging which ones are interesting.',
  },
  other: { title: 'Earlier work', blurb: '' },
};

export const papers: Paper[] = [
  {
    title: 'Harness as a Language: A Minimalist Agent Framework With Maximal Expressivity',
    authors:
      'Z. Li, J. Liu, M. Vukelic, N. Shen, S. Lall, Amitayush Thakur, A. Zhang, O. Khattab, J. Light, A. Solar-Lezama',
    venue: 'Preprint',
    year: 2026,
    theme: 'neurosymbolic',
    links: [{ label: 'arXiv', href: 'https://arxiv.org/abs/2609.26891' }],
  },
  {
    title: 'ProofWala: A Framework for Multilingual Proof Data Synthesis and Theorem-Proving',
    authors: 'Amitayush Thakur, George Tsoukalas, Greg Durrett, Swarat Chaudhuri',
    venue: 'ITP 2026',
    year: 2026,
    theme: 'agents',
    selected: true,
    thumbnail: '/assets/img/2025-02-07-ProofWala/thumbnail.png',
    links: [
      { label: 'Paper', href: 'https://doi.org/10.4230/LIPIcs.ITP.2026.24' },
      { label: 'arXiv', href: 'https://arxiv.org/abs/2502.04671' },
      { label: 'Code', href: 'https://github.com/trishullab/proof-wala' },
    ],
  },
  {
    title: 'CLEVER: A Curated Benchmark for Formally Verified Code Generation',
    authors:
      'Amitayush Thakur, Jasper Lee, George Tsoukalas, Meghana Sistla, Matthew Zhao, Stefan Zetzsche, Greg Durrett, Yisong Yue, Swarat Chaudhuri',
    venue: 'NeurIPS 2025',
    year: 2025,
    theme: 'verified-code',
    selected: true,
    thumbnail: '/assets/img/2025-06-11-CLEVER/thumbnail.png',
    links: [
      { label: 'arXiv', href: 'https://arxiv.org/abs/2505.13938' },
      { label: 'Code', href: 'https://github.com/trishullab/clever' },
    ],
  },
  {
    title: 'Learning Interestingness in Automated Mathematical Theory Formation',
    authors: 'George Tsoukalas, Rahul Saha, Amitayush Thakur, Sabrina Reguyal, Swarat Chaudhuri',
    venue: 'NeurIPS 2025',
    year: 2025,
    theme: 'neurosymbolic',
    award: 'Spotlight',
    selected: true,
    thumbnail: '/assets/img/2025-11-27-LearningInterestingness/thumbnail.png',
    links: [
      { label: 'arXiv', href: 'https://arxiv.org/abs/2511.14778' },
      { label: 'Code', href: 'https://github.com/trishullab/Fermat' },
    ],
  },
  {
    title: 'PutnamBench: Evaluating Neural Theorem-Provers on the Putnam Mathematical Competition',
    authors:
      'George Tsoukalas, Jasper Lee, John Jennings, Jimmy Xin, Michelle Ding, Michael Jennings, Amitayush Thakur, Swarat Chaudhuri',
    venue: 'NeurIPS 2024',
    year: 2024,
    theme: 'agents',
    award: 'Best Paper, AI for Math Workshop @ ICML 2024',
    selected: true,
    thumbnail: '/assets/img/thumbnails/putnam_bench_thumbnail.png',
    links: [
      { label: 'Website', href: 'https://trishullab.github.io/PutnamBench/' },
      { label: 'arXiv', href: 'https://arxiv.org/abs/2407.11214' },
      { label: 'Code', href: 'https://github.com/trishullab/PutnamBench' },
    ],
  },
  {
    title: 'An In-Context Learning Agent for Formal Theorem-Proving',
    authors: 'Amitayush Thakur, George Tsoukalas, Yeming Wen, Jimmy Xin, Swarat Chaudhuri',
    venue: 'COLM 2024',
    year: 2024,
    theme: 'agents',
    selected: true,
    thumbnail: '/assets/img/2023-10-09-AutomaticTheoremProvingAndLanguageAgents/thumbnail.png',
    links: [
      { label: 'Blog', href: '/blog/copra' },
      { label: 'arXiv', href: 'https://arxiv.org/abs/2310.04353' },
      { label: 'Code', href: 'https://github.com/trishullab/copra' },
    ],
  },
  {
    title: 'A Distributed Algorithm for Balanced Multi-Robot Task Allocation',
    authors: 'A. Gautam, Amitayush Thakur, G. Dhanania, S. Mohan',
    venue: 'ICIIS 2016',
    year: 2016,
    theme: 'other',
    links: [{ label: 'IEEE', href: 'https://doi.org/10.1109/ICIINFS.2016.8263014' }],
  },
];
