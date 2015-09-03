/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package chat;

import java.awt.FlowLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTabbedPane;

/**
 *
 * @author Amber
 */
public class CloseTab extends JPanel implements ActionListener {

	String title;
	ChatTabbedPanel chatTabbedPanel;

	public CloseTab(ChatTabbedPanel chatTabbedPanel, String title, boolean enabled) {


		this.title = title;
		this.chatTabbedPanel = chatTabbedPanel;

		add(new JLabel(title));

		if (enabled) {
			JButton button = new JButton("x");

			button.addActionListener(this);

			button.setMargin(new Insets(0, 0, 0, 0));

			add(button);
		}
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		chatTabbedPanel.getChatTabbedModel().removeChat(chatTabbedPanel.getChatPanes().getTitleAt(chatTabbedPanel.getChatPanes().indexOfTabComponent(this)));
		chatTabbedPanel.getChatPanes().remove(chatTabbedPanel.getChatPanes().indexOfTabComponent(this));
	}
}
