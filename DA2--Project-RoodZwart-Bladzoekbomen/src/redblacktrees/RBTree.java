/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Stack;

public class RBTree implements Tree {

	private MyVertex root;
	private Stack<MyVertex> track;

	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////     ADD FUNCTIONS      //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public boolean add(int value) {
		///////////////////////
		////  WITH A STACK ////
		///////////////////////
//		return stackAdd(value);

		///////////////////////
		////  WITH PARENTS ////
		///////////////////////
		return parentAdd(value); // Faster!
	}

	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////  PARENTADD FUNCTIONS   //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	public boolean parentAdd(int value) {

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
				parentRebalance(toAdd);
			}

		}
		return true;
	}

	public void parentRebalance(MyVertex newChild) {
		while (newChild != root && newChild.getParent().getColor() == Vertex.RED) {

			int childValue = newChild.getValue();
			int parentValue = newChild.getParent().getValue();
			int grandParentValue = newChild.getParent().getParent().getValue();

			if (childValue < parentValue) {
				if (parentValue < grandParentValue) {
					newChild = parentRebalanceLL(newChild);
				} else {
					newChild = parentRebalanceRL(newChild);
				}
			} else {
				if (parentValue < grandParentValue) {
					newChild = parentRebalanceLR(newChild);
				} else {
					newChild = parentRebalanceRR(newChild);
				}
			}

			coloring(newChild.getLeft(), newChild.getRight(), newChild);
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
	public MyVertex parentRebalanceLL(MyVertex child) {
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
	public MyVertex parentRebalanceRL(MyVertex child) {
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
	public MyVertex parentRebalanceLR(MyVertex child) {
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
	public MyVertex parentRebalanceRR(MyVertex child) {
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

		return parent;
	}

	public void coloring(MyVertex child, MyVertex child2, MyVertex newParent) {
		newParent.setColor(Vertex.RED);

		child.setColor(Vertex.BLACK);
		child2.setColor(Vertex.BLACK);
	}

	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////   STACKADD FUNCTIONS   //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	public boolean stackAdd(int value) {
		track = new Stack<MyVertex>();

		if (root == null) {
			root = new MyVertex(Vertex.BLACK, value, null, null, null);
			return true;
		} else {
			track.push(root);
			MyVertex vertexToAdd = new MyVertex(Vertex.RED, value, null, null, null);
			while (track.peek() != null) {
				if (value < track.peek().getValue()) {
					if (track.peek().getLeft() == null) {
						track.peek().setLeft(vertexToAdd);
						if (track.peek().getColor() != Vertex.RED) {
							return true;
						}
						break;
					}
					track.push(track.peek().getLeft());
				} else if (value > track.peek().getValue()) {
					if (track.peek().getRight() == null) {
						track.peek().setRight(vertexToAdd);
						if (track.peek().getColor() != Vertex.RED) {
							return true;
						}
						break;
					}
					track.push(track.peek().getRight());
				} else {
					return false;
				}
			}

			stackRebalance(vertexToAdd);

		}
		return true;
	}

	public void stackRebalance(MyVertex newChild) {
		while (newChild != root && track.peek().getColor() == Vertex.RED) {
			MyVertex parent = track.pop();
			MyVertex grandParent = track.pop();

			int childValue = newChild.getValue();
			int parentValue = parent.getValue();
			int grandParentValue = grandParent.getValue();

			if (childValue < parentValue) {
				if (parentValue < grandParentValue) {
					newChild = stackRebalanceLL(newChild, parent, grandParent);
				} else {
					newChild = stackRebalanceRL(newChild, parent, grandParent);
				}
			} else {
				if (parentValue < grandParentValue) {
					newChild = stackRebalanceLR(newChild, parent, grandParent);
				} else {
					newChild = stackRebalanceRR(newChild, parent, grandParent);
				}
			}
		}

		if (newChild == root && newChild.getColor() == Vertex.RED) {
			newChild.setColor(Vertex.BLACK);
		}

		track = null; // Leeg de stack als er nog waarden op zitten om geheugen te besparen
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
	public MyVertex stackRebalanceLL(MyVertex child, MyVertex parent, MyVertex grandParent) {

		grandParent.setLeft(parent.getRight());
		parent.setRight(grandParent);

		if (grandParent == root) {
			root = parent;
		} else {
			if (parent.getValue() > track.peek().getValue()) {
				track.peek().setRight(parent);
			} else {
				track.peek().setLeft(parent);
			}
		}

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
	public MyVertex stackRebalanceRL(MyVertex child, MyVertex parent, MyVertex grandParent) {

		grandParent.setRight(child.getLeft());
		parent.setLeft(child.getRight());

		child.setLeft(grandParent);
		child.setRight(parent);

		if (grandParent == root) {
			root = child;
		} else {
			if (child.getValue() > track.peek().getValue()) {
				track.peek().setRight(child);
			} else {
				track.peek().setLeft(child);
			}
		}
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
	public MyVertex stackRebalanceLR(MyVertex child, MyVertex parent, MyVertex grandParent) {
		grandParent.setLeft(child.getRight());
		parent.setRight(child.getLeft());

		child.setRight(grandParent);
		child.setLeft(parent);

		if (grandParent == root) {
			root = child;
		} else {
			if (child.getValue() > track.peek().getValue()) {
				track.peek().setRight(child);
			} else {
				track.peek().setLeft(child);
			}
		}

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
	 *        b2  C(r)   b1|b2|b3|b4
	 *           / \
	 *          b3  b4 
	 */
	public MyVertex stackRebalanceRR(MyVertex child, MyVertex parent, MyVertex grandParent) {

		grandParent.setRight(parent.getLeft());
		parent.setLeft(grandParent);

		if (grandParent == root) {
			root = parent;
		} else {
			if (parent.getValue() > track.peek().getValue()) {
				track.peek().setRight(parent);
			} else {
				track.peek().setLeft(parent);
			}
		}

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
	/////////////////////////////////   CONTAINS  FUNCTION   //////////////////////////////////
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
	Stack<MyVertex> stack;
	ArrayList<Integer> valueList;

	@Override
	public Iterator<Integer> iterator() {
		///////////////////////
		/////  RECURSIVE  /////
		///////////////////////

//		valueList = new ArrayList<Integer>();
//		if (root != null) {
//			recursiveIterator(root);
//		}
//		return valueList.iterator();

		///////////////////////
		/////  WITH STACK /////
		///////////////////////
//		stack = new Stack<MyVertex>();
//		valueList = new ArrayList<Integer>();
//
//		stackIterator(root);
//
//		return valueList.iterator();

		///////////////////////
		////  WITCH CLASS  ////
		///////////////////////
		return new TreeIterator(root);  // Faster!
	}

	public void recursiveIterator(MyVertex vertex) {
		if (vertex.getLeft() != null) {
			recursiveIterator(vertex.getLeft());
		}
		valueList.add(vertex.getValue());
		if (vertex.getRight() != null) {
			recursiveIterator(vertex.getRight());
		}
	}

	public void stackIterator(MyVertex vertex) {
		MyVertex temp;

		stack.push(vertex);

		while (stack.peek().getLeft() != null) {
			stack.push(stack.peek().getLeft());
		}
		while (stack.size() != 0) {

			valueList.add(stack.peek().getValue());

			if (stack.peek().getRight() != null) {
				temp = stack.pop();
				stackIterator(temp.getRight());
			} else {
				stack.pop();
			}
		}
	}

	///////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////    GETTERS & SETTERS     /////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public MyVertex root() {
		return root;
	}

	public void setRoot(MyVertex vertex) {
		root = vertex;
	}
}
