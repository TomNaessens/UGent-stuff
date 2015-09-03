package redblacktrees;

// Do not alter this file in any way!
public interface Vertex {

    static final int RED = 0;
    static final int BLACK = 1;

    /**
     * Return the color of this vertex
     * RED is 0
     * BLACK is 1
     * @return the color of this vertex
     */
    public int getColor();

    /**
     * return the value located in this vertex
     *
     * @return the value of this vertex
     */
    public int getValue();

    /**
     * @return the left child of this vertex or NULL if this vertex has no left
     * child
     */
    public Vertex getLeft();

    /**
     * @return the right child of this vertex or NULL if this vertex has no
     * right child
     */
    public Vertex getRight();

}
