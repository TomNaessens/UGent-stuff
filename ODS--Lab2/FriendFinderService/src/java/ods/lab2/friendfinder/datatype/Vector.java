package ods.lab2.friendfinder.datatype;

/**
 * Represents a math based Vector
 * @author fdebacke
 *
 */


public class Vector {

	//Starting point
	private Point start;
	
	//Length of the vector
	double length;
	
	//Direction of the vector
	double direction;
	
	public Vector(Point start, double length, double direction){
		this.start=start;
		this.length=length;
		this.direction=direction;
	}
	
	public Vector(Point start,Point end){
		this.start=start;
		length = start.distance(end);
		direction = calculateAngle(start,end);
	}
	 
	
	/**
	 * Calculates the dot product of two vectors
	 * @param b
	 * @return
	 */
	public double dotProduct(Vector b){
		double angle = Math.abs(direction-b.getDirection());
		return getLength()*b.getLength()*Math.cos(angle);
	}
	
	
	/**
	 * Calculates the angle between a line and the horizontal X-axis. 
	 * @param a first point defining the line
	 * @param b second point defining the line
	 * @return the angle in radians
	 */
    public double calculateAngle(Point a, Point b)
    {
        double dx = b.getX()-a.getX();
        double dy = b.getY()-a.getY();
        double angle=0.0d;
 
        // Calculate angle
        if (dx == 0.0)
        {
            if (dy == 0.0)
                angle = 0.0;
            else if (dy > 0.0)
                angle = Math.PI / 2.0;
            else
                angle = Math.PI * 3.0 / 2.0;
        }
        else if (dy == 0.0)
        {
            if  (dx > 0.0)
                angle = 0.0;
            else
                angle = Math.PI;
        }
        else
        {
            if  (dx < 0.0)
                angle = Math.atan(dy/dx) + Math.PI;
            else if (dy < 0.0)
                angle = Math.atan(dy/dx) + (2*Math.PI);
            else
                angle = Math.atan(dy/dx);
        }
 
        return angle;
    }

    
    /**
     * Returns the starting point of the vector
     * @return
     */
	public Point getStart() {
		return start;
	}
	
	/**
	 * Moves the vector to a different starting point
	 * @param start
	 */
	public void setStart(Point start) {
		this.start = start;
	}

	
	/**
	 * Returns the length of the vector
	 * @return
	 */
	public double getLength() {
		return length;
	}

	
	/**
	 * Changes the length of the vector
	 * @param length
	 */
	public void setLength(double length) {
		this.length = length;
	}

	
	/**
	 * Returns the angle of the vector in radians
	 * @return
	 */
	public double getDirection() {
		return direction;
	}
	
	
	/**
	 * Changes the angle of the vector
	 * @param direction the new angle in radians
	 */
	public void setDirection(double direction) {
		this.direction = direction;
	}

}
