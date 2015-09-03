/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

import java.util.Iterator;
import java.util.Stack;

public class TreeIterator implements Iterator {

	private Stack<MyVertex> stack;

	public TreeIterator(MyVertex root) {
		stack = new Stack<MyVertex>();

		addLeft(root);
	}

	@Override
	public boolean hasNext() {
		return (stack.size() != 0);
	}

	@Override
	// returns the next value in the tree (in ascending order)
	public Object next() {
		MyVertex temp = stack.pop();

		if (temp.getRight() != null) {
			addLeft(temp.getRight());
		}

		return temp.getValue();
	}

	// Adds the left childs of the vertex
	public void addLeft(MyVertex vertex) {
		if (vertex != null) {
			stack.push(vertex);
			if (vertex.getLeft() != null) {
				addLeft(vertex.getLeft());
			}
		}
	}

	@Override
	public void remove() {
		throw new UnsupportedOperationException("Not supported yet.");
	}

	public Stack<MyVertex> getStack() {
		return stack;
	}
}
