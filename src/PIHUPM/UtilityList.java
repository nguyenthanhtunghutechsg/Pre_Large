package PIHUPM;

/* This file is copyright (c) 2008-2013 Philippe Fournier-Viger
* 
* This file is part of the SPMF DATA MINING SOFTWARE
* (http://www.philippe-fournier-viger.com/spmf).
* 
* SPMF is free software: you can redistribute it and/or modify it under the
* terms of the GNU General Public License as published by the Free Software
* Foundation, either version 3 of the License, or (at your option) any later
* version.
* 
* SPMF is distributed in the hope that it will be useful, but WITHOUT ANY
* WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
* A PARTICULAR PURPOSE. See the GNU General Public License for more details.
* You should have received a copy of the GNU General Public License along with
* SPMF. If not, see <http://www.gnu.org/licenses/>.
*/


import java.util.ArrayList;
import java.util.List;

/**
 * This class represents a UtilityList as used by the HUI-Miner algorithm.
 *
 * @see Element
 * @author Philippe Fournier-Viger
 */
public class UtilityList {

	// the last item of the itemset represented by this utility list
	public Integer item;
	// the sum of iutil values of D
	public int sumIutils = 0;
	// the sum of rutil values  of D
	public int sumRutils = 0;


	// the list of elements in this utility list
	public List<Element> elements = new ArrayList<Element>();

	/**
	 * Constructor
	 * @param item the last item of the itemset represented by this utility list
	 */
	public UtilityList(Integer item) {
		super();
		this.item = item;
	}

	/**
	 * Method to add an element to this utility list and update the sums at the same time.
	 * @param element the element to be added
	 */
	public void addElement(Element element){
		sumIutils += element.iutils;
		sumRutils += element.rutils;
		elements.add(element);
	}
}
