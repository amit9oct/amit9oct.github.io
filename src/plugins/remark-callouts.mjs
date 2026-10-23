import { visit } from 'unist-util-visit';

// Turns `:::theorem[Optional title]` ... `:::` into a styled callout block.
const KINDS = ['definition', 'theorem', 'lemma', 'remark', 'problem', 'note', 'example'];

export function remarkCallouts() {
  return (tree) => {
    visit(tree, (node) => {
      if (node.type !== 'containerDirective' || !KINDS.includes(node.name)) return;

      let title = '';
      const first = node.children[0];
      if (first?.data?.directiveLabel) {
        title = first.children.map((c) => c.value ?? '').join('');
        node.children.shift();
      }
      const label = node.name[0].toUpperCase() + node.name.slice(1);

      node.data = {
        hName: 'div',
        hProperties: { className: ['callout', `callout-${node.name}`] },
      };
      node.children.unshift({
        type: 'paragraph',
        data: { hName: 'p', hProperties: { className: ['callout-label'] } },
        children: [
          { type: 'strong', children: [{ type: 'text', value: label }] },
          ...(title ? [{ type: 'text', value: ` (${title})` }] : []),
          { type: 'text', value: '.' },
        ],
      });
    });
  };
}
