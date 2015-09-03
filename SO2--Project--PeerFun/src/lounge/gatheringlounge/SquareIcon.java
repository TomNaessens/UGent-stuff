/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package lounge.gatheringlounge;

import java.awt.Color;
import java.awt.Component;
import java.awt.Graphics;
import javax.swing.Icon;

public class SquareIcon implements Icon {

	Color color;
	int iconHeight;
	int iconWidth;
	int x;
	int y;

	public SquareIcon(Color color, int x, int y, int iconWidth, int iconHeight) {
		this.color = color;
		this.iconHeight = iconHeight;
		this.iconWidth = iconWidth;
		this.x = x;
		this.y = y;
	}

	@Override
	public void paintIcon(Component cmpnt, Graphics g, int i, int i1) {
		g.setColor(color);
		g.fillRect(x, y-iconHeight/2, iconWidth, iconHeight);
		g.setColor(Color.BLACK);
		g.drawRect(x, y-iconHeight/2, iconWidth, iconHeight);
	}

	@Override
	public int getIconWidth() {
		return iconWidth;
	}

	@Override
	public int getIconHeight() {
		return iconHeight;
	}

	void setHeight(int height) {
		this.iconHeight = height;
	}
	
	void setWidth(int width) {
		this.iconWidth = width;
	}

}
