// Newest first. `date` is free text, e.g. "Oct 2025" or just "2026".
export const news: { date: string; html: string }[] = [
  { date: '2026', html: 'New preprint: <a href="https://arxiv.org/abs/2609.26891">Harness as a Language</a>, a minimalist agent framework.' },
  { date: 'May 2026', html: 'Started an Applied Science internship at <b>Amazon</b> with the Automated Reasoning Group, working on agent-based proof automation for software verification.' },
  { date: '2026', html: '<b>ProofWala</b> accepted at <a href="https://doi.org/10.4230/LIPIcs.ITP.2026.24">ITP 2026</a>.' },
  { date: 'Oct 2025', html: 'Invited talk at Amazon’s Automated Reasoning Symposium: “End-to-End Verified Code Generation in Lean.”' },
  { date: '2025', html: '<b>CLEVER</b> and <b>Learning Interestingness</b> (Spotlight) accepted at NeurIPS 2025.' },
  { date: 'Jul 2025', html: 'Talk at TPC25 (Trillion Parameter Consortium) on CLEVER.' },
  { date: 'May 2025', html: 'Machine Learning intern at <b>Asari AI</b>, San Francisco.' },
  { date: '2024', html: 'Received the <b>Amazon Automated Reasoning Fellowship</b> from the UT–Amazon Science Hub.' },
  { date: 'Jul 2024', html: '<b>PutnamBench</b> won Best Paper at the AI for Math Workshop at ICML 2024.' },
];

export const experience = [
  { when: '2026', org: 'Amazon Science', role: 'Applied Science Intern', note: 'Automated Reasoning Group' },
  { when: '2025', org: 'Asari AI', role: 'ML Intern', note: 'Agents for complex systems design' },
  { when: '2017–22', org: 'Microsoft Azure', role: 'Software Engineer II', note: 'Distributed backup services, TLA+' },
  { when: '2017', org: 'Microsoft Research', role: 'Research Intern', note: 'Program synthesis (PROSE)' },
  { when: '2016', org: 'Microsoft Azure', role: 'Summer Intern', note: 'Azure Backup team' },
  { when: '2014', org: 'Bhabha Atomic Research Centre', role: 'Project Trainee', note: 'Network management system' },
];

export const talks = [
  { date: 'Oct 2025', venue: 'Amazon Automated Reasoning Symposium', title: 'End-to-End Verified Code Generation in Lean' },
  { date: 'Jul 2025', venue: 'TPC25, Trillion Parameter Consortium', title: 'CLEVER: A Benchmark for Two-staged, End-to-end Verified Code Generation' },
  { date: 'Feb 2024', venue: 'Rutgers, Department of Mathematics', title: 'Advancing Theorem Proving with AI: The Power of Large Language Models' },
];
