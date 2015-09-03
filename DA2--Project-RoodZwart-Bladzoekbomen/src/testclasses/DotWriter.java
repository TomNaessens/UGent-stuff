/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package testclasses;

import redblacktrees.MyVertex;
import redblacktrees.Vertex;

public class DotWriter {

	public DotWriter() {
		System.out.println("digraph graphName {");
		System.out.println("node [shape = record];");
	}

	public void addNode(MyVertex vertex) {
		if (vertex != null) {
			String color;
			String fontcolor;
			if (vertex.getColor() == Vertex.RED) {
				color = "red";
				fontcolor = "red";
			} else if (vertex.getColor() == Vertex.BLACK) {
				color = "black";
				fontcolor = "black";
			} else {
				color = "white";
				fontcolor = "black";
			}

			System.out.println("node" + vertex.hashCode() + " [label = \"<f0> | <f1> " + vertex.getValue() + " | <f2> \", color = " + color + ", fontcolor = " + fontcolor + "];");
			if (vertex.getLeft() != null) {
				System.out.println("\"node" + vertex.hashCode() + "\":f0 -> \"node" + vertex.getLeft().hashCode() + "\":f1;");
				addNode(vertex.getLeft());
			}
			if (vertex.getRight() != null) {
				System.out.println("\"node" + vertex.hashCode() + "\":f2 -> \"node" + vertex.getRight().hashCode() + "\":f1;");
				addNode(vertex.getRight());
			}
		} else {
			
		}
	}

	public void closeWriter() {
		System.out.println("}");
	}
}
