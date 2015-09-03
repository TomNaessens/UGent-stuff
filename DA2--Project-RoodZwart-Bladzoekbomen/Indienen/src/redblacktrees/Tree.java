package redblacktrees;

import java.util.Iterator;

// Do not alter this file in any way!
public interface Tree {

    /**
     * Inserts a new value into the tree
     *
     * @param value the new value
     * @return true if the value was not already in the set, false otherwise
     */
    public boolean add(int value);

    /**
     * Removes a value from the tree
     *
     * @param value value to be removed
     * @return true if the value was present before removal, false if it was not
     * present
     */
    public boolean remove(int value);

    /**
     * Check if the tree contains a certain value
     *
     * @param value value to be checked
     * @return true if the key is contained in the tree, else false
     */
    public boolean contains(int value);

    /**
     * Get the root of the tree
     *
     * @return a Vertex object, which is the root of the tree
     * @see Vertex
     */
    public Vertex root();

    /**
     * Return an iterator that traverses all keys in ascending order
     *
     * @return an iterator over all keys
     */
    public Iterator<Integer> iterator();

}