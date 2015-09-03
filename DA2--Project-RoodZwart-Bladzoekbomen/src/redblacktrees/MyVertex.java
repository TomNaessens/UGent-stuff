/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

public class MyVertex implements Vertex {


	// VARIABLES
	static final int NOCOLOR = -1;
	
	private int color;		// 0 = RED, 1 = BLACK
	private int value;		// Top value
	private MyVertex parent;	// Parent
	private MyVertex left;	// Left child
	private MyVertex right;	// Right child
	
	// CONSTRUCTOR
	public MyVertex(int color, int value, MyVertex parent, MyVertex left, MyVertex right) {
		this.color = color;
		this.value = value;
		this.parent = parent;
		this.left = left;
		this.right = right;
	}
	
	// GETTERS
	@Override
	public int getColor() {
		return color;
	}

	@Override
	public int getValue() {
		return value;
	}

	@Override
	public MyVertex getLeft() {
		return left;
	}

	@Override
	public MyVertex getRight() {
		return right;
	}
	
	public MyVertex getParent() {
		return parent;
	}
	
	// SETTERS
	public void setColor(int color) {
		this.color = color;
	}
	
	public void setLeft(MyVertex left) {
		this.left = left;
	}
	
	public void setRight(MyVertex right) {
		this.right = right;
	}
	
	public void setParent(MyVertex parent) {
		this.parent = parent;
	}
	
	public void setValue(int value) {
		this.value = value;
	}
	
}
