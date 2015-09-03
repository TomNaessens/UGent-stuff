package ods.lab2.friendfinder.datatype;

/**
 * Represents a point in the 2 dimensional euclidean space
 * @author fdebacke
 *
 */

public class Point {

	//X-coordinate
	private double x;
	
	//Y-coordinate	
	private double y;
	
	public Point(double x,double y){
		this.x=x;
		this.y=y;
	}

	public double getX() {
		return x;
	}

	public void setX(double x) {
		this.x = x;
	}

	public double getY() {
		return y;
	}

	public void setY(double y) {
		this.y = y;
	}
	
	/**
	 * Calculates the distance between two 2-dimensional point
	 * @param b the second point
	 * @return the distance in the euclidean space
	 */
	public double distance(Point b){
		return Math.sqrt(Math.pow(b.getX()-x,2)+Math.pow(b.getY()-y,2));
	}
	
}

