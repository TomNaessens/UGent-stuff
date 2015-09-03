/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

public class LeafIterator extends TreeIterator {

	public LeafIterator(MyVertex root) {
		super(root);
	}

	@Override
	public Object next() {
		MyVertex temp = super.getStack().pop();

		if (super.getStack().size() > 0) {
			while (super.getStack().peek().getRight() == null) {
				super.getStack().pop();
			}
			addLeft(super.getStack().pop().getRight());
		}

		return temp.getValue();
	}
}
