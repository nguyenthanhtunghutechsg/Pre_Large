package Pre_TK_INC;

/* This file is copyright (c) 2008-2015 Srikumar Krishnamoorty
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
public class PatternTHUI implements Comparable<PatternTHUI>{
	
	int[] prefix;
	int item;
	long utility;
	int sup;
	int idx;//for sorting patterns in order of insertion 
	
	public PatternTHUI(int[] prefix, UtilityList X, int idx) {
//		for (int i = 0; i < length; i++) {
//			buffer += prefix[i];
//			buffer += " ";
//		}
		item = X.item;
		this.prefix = prefix;
		this.idx = idx;
		
		this.utility = X.getUtils();
		this.sup = X.elements.size();// + X.sup;//X.sup for closed items
	}
	public PatternTHUI(int[] prefix, int item, long utility) {
		this.item = item;
		this.prefix = prefix;
		this.utility = utility;
	}

	public int[] getPrefix(){
		return this.prefix;
	}

	public int compareTo(PatternTHUI o) {
		if(o == this){
			return 0;
		}
		long compare = this.utility - o.utility;
		if(compare !=0){
			return (int) compare;
		}
		return this.hashCode() - o.hashCode();
	}

}
