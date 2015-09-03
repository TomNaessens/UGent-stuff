/**
 * Tree1:
 *	Normal red-black tree
 *	Functions:
 *		add (uses rebalance, rebalanceLL, rebalanceLR, rebalanceRL, rebalanceRR as helpmethods)
 *		contains
 *		iterator (returns an object of class TreeIterator)
 *		root (returns the root)
 *	All methods use objects of the class MyVertex as Vertexes
 * 
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

import java.util.Iterator;

public class Tree1 implements Tree {

	private MyVertex root;
	
	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////     ADD FUNCTIONS      //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public boolean add(int value) {
		if (root == null) {
			root = new MyVertex(Vertex.BLACK, value, null, null, null);
			return true;
		} else {
			MyVertex vertex = root;
			MyVertex toAdd = new MyVertex(Vertex.RED, value, null, null, null);

			while (vertex != null) {
				toAdd.setParent(vertex);
				if (value < vertex.getValue()) {
					vertex = vertex.getLeft();
				} else if (value > vertex.getValue()) {
					vertex = vertex.getRight();
				} else {
					return false;
				}
			}

			if (toAdd.getValue() < toAdd.getParent().getValue()) {
				toAdd.getParent().setLeft(toAdd);
			} else {
				toAdd.getParent().setRight(toAdd);
			}

			if (toAdd.getParent().getColor() == Vertex.RED) {
				rebalance(toAdd);
			}

		}
		return true;
	}

	public void rebalance(MyVertex newChild) {
		while (newChild != root && newChild.getParent().getColor() == Vertex.RED) {

			int childValue = newChild.getValue();
			int parentValue = newChild.getParent().getValue();
			int grandParentValue = newChild.getParent().getParent().getValue();

			if (childValue < parentValue) {
				if (parentValue < grandParentValue) {
					newChild = rebalanceLL(newChild);
				} else {
					newChild = rebalanceRL(newChild);
				}
			} else {
				if (parentValue < grandParentValue) {
					newChild = rebalanceLR(newChild);
				} else {
					newChild = rebalanceRR(newChild);
				}
			}
		}

		if (newChild == root && newChild.getColor() == Vertex.RED) {
			newChild.setColor(Vertex.BLACK);
		}

	}

	/* LL: Left Left
	 * Parent(B) is left of grandparent(A)
	 * Child(C) is left of Parent(B)
	 *        A(z)			B(r)
	 *       / \		    / \
	 *   (r)B   b4      (z)C   A(z)
	 *     / \            / \ / \		
	 * (r)C   b3        b1|b2|b3|b4
	 *   / \
	 *  b1  b2
	 */
	public MyVertex rebalanceLL(MyVertex child) {
		MyVertex parent = child.getParent();
		MyVertex grandParent = parent.getParent();

		grandParent.setLeft(parent.getRight());

		if (parent.getRight() != null) {
			parent.getRight().setParent(grandParent);
		}

		parent.setRight(grandParent);

		if (grandParent == root) {
			root = parent;
			parent.setParent(null);
		} else {
			if (parent.getValue() > grandParent.getParent().getValue()) {
				grandParent.getParent().setRight(parent);
			} else {
				grandParent.getParent().setLeft(parent);
			}
			parent.setParent(grandParent.getParent());
		}

		child.setParent(parent);
		grandParent.setParent(parent);

		child.setColor(Vertex.BLACK);
		parent.setColor(Vertex.RED);
		grandParent.setColor(Vertex.BLACK);

		return parent;
	}

	/* RL: Left Left
	 * Parent(B) is right of grandparent(A)
	 * Child(C) is left of Parent(B)
	 *        A(z)			C(r)
	 *       / \		    / \
	 *      b1   B(r)   (z)A   B(z)
	 *          / \       / \ / \	
	 *      (r)C   b4   b1|b2|b3|b4
	 *        / \
	 *       b2  b3	  
	 */
	public MyVertex rebalanceRL(MyVertex child) {
		MyVertex parent = child.getParent();
		MyVertex grandParent = parent.getParent();

		grandParent.setRight(child.getLeft());
		parent.setLeft(child.getRight());

		if (child.getLeft() != null) {
			child.getLeft().setParent(grandParent);
		}
		if (child.getRight() != null) {
			child.getRight().setParent(parent);
		}

		child.setLeft(grandParent);
		child.setRight(parent);

		if (grandParent == root) {
			root = child;
			child.setParent(null);
		} else {
			if (child.getValue() > grandParent.getParent().getValue()) {
				grandParent.getParent().setRight(child);
			} else {
				grandParent.getParent().setLeft(child);
			}
			child.setParent(grandParent.getParent());
		}

		parent.setParent(child);
		grandParent.setParent(child);

		parent.setColor(Vertex.BLACK);
		child.setColor(Vertex.RED);
		grandParent.setColor(Vertex.BLACK);

		return child;
	}

	/* LR: Left Left
	 * Parent(B) is left of grandparent(A)
	 * Child(C) is right of Parent(B)
	 *        A(z)			C(r)
	 *       / \		    / \
	 *   (r)B   b4      (z)B   A(z)
	 *     / \            / \ / \
	 *    b1  C(r)      b1|b2|b3|b4
	 *       / \
	 *      b2  b3
	 */
	public MyVertex rebalanceLR(MyVertex child) {
		MyVertex parent = child.getParent();
		MyVertex grandParent = parent.getParent();

		grandParent.setLeft(child.getRight());
		parent.setRight(child.getLeft());

		if (child.getRight() != null) {
			child.getRight().setParent(grandParent);
		}
		if (child.getLeft() != null) {
			child.getLeft().setParent(parent);
		}

		child.setRight(grandParent);
		child.setLeft(parent);

		if (grandParent == root) {
			root = child;
			child.setParent(null);
		} else {
			if (child.getValue() > grandParent.getParent().getValue()) {
				grandParent.getParent().setRight(child);
			} else {
				grandParent.getParent().setLeft(child);
			}
			child.setParent(grandParent.getParent());
		}

		parent.setParent(child);
		grandParent.setParent(child);

		parent.setColor(Vertex.BLACK);
		child.setColor(Vertex.RED);
		grandParent.setColor(Vertex.BLACK);

		return child;
	}

	/* RR: Right right
	 * Parent(B) is right of grandparent(A)
	 * Child(C) is right of Parent(B)
	 *        A(z)			B(r)
	 *       / \		    / \
	 *      b1  B(r)    (z)A   C(z)
	 *         / \        / \ / \
	 *        b2  C(r)  b1|b2|b3|b4
	 *           / \
	 *          b3  b4 
	 */
	public MyVertex rebalanceRR(MyVertex child) {
		MyVertex parent = child.getParent();
		MyVertex grandParent = parent.getParent();

		grandParent.setRight(parent.getLeft());

		if (parent.getLeft() != null) {
			parent.getLeft().setParent(grandParent);
		}

		parent.setLeft(grandParent);


		if (grandParent == root) {
			root = parent;
			parent.setParent(null);
		} else {
			if (parent.getValue() > grandParent.getParent().getValue()) {
				grandParent.getParent().setRight(parent);
			} else {
				grandParent.getParent().setLeft(parent);
			}
			parent.setParent(grandParent.getParent());
		}

		child.setParent(parent);
		grandParent.setParent(parent);

		child.setColor(Vertex.BLACK);
		parent.setColor(Vertex.RED);
		grandParent.setColor(Vertex.BLACK);

		return parent;
	}
	
	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////    REMOVE FUNCTIONS    //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public boolean remove(int value) {
		throw new UnsupportedOperationException("Not supported yet.");
	}

	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////   CONTAINS FUNCTIONS   //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public boolean contains(int value) {
		MyVertex vertex = root;
		while (vertex != null) {
			if (value < vertex.getValue()) {
				vertex = vertex.getLeft();
			} else if (value > vertex.getValue()) {
				vertex = vertex.getRight();
			} else {
				return true;
			}
		}
		return false;
	}


	///////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////    ITERATOR FUNCTIONS    /////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public Iterator<Integer> iterator() {
		return new TreeIterator(root);
	}
		
	
	///////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////    GETTERS & SETTERS     /////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public MyVertex root() {
		return root;
	}
}
