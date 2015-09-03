/*
 * Implementatie van een gewone rood-zwart boom die de kleuring van op p. 23 gebruikt wanneer mogelijk
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

public class Tree2 extends AbstractRBTree {

	@Override
	public void rebalance(MyVertex vertex) {
		variantRebalance(vertex);
	}
}