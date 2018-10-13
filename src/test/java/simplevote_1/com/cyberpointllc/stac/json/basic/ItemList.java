/*
 * $Id: ItemList.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-3-24
 */
package simplevote_1.com.cyberpointllc.stac.json.basic;

import java.util.ArrayList;
import java.util.List;

/**
 * |a:b:c| => |a|,|b|,|c|
 * |:| => ||,||
 * |a:| => |a|,||
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class ItemList {
    private final ItemListHelper itemListHelper = new ItemListHelper(this);
    private String sp=",";
	List items=new ArrayList();
	
	
	public ItemList(){}
	
	
	public ItemList(String s){
		this.split(s,sp,items);
	}
	
	public ItemList(String s,String sp){
		this.sp=s;
		this.split(s,sp,items);
	}
	
	public ItemList(String s,String sp,boolean isMultiToken){
        itemListHelper.split(s, sp, items, isMultiToken);
	}
	
	public List fetchItems(){
		return this.items;
	}
	
	public String[] pullArray(){
		return (String[])this.items.toArray();
	}
	
	public void split(String s,String sp,List append,boolean isMultiToken){
        itemListHelper.split(s, sp, append, isMultiToken);
    }
	
	public void split(String s,String sp,List append){
		if(s==null || sp==null)
			return;
		int pos=0;
		int prevPos=0;
		do{
			prevPos=pos;
			pos=s.indexOf(sp,pos);
			if(pos==-1)
				break;
			append.add(s.substring(prevPos,pos).trim());
			pos+=sp.length();
		}while(pos!=-1);
		append.add(s.substring(prevPos).trim());
	}
	
	public void defineSP(String sp){
		this.sp=sp;
	}
	
	public void add(int j, String item){
        itemListHelper.add(j, item);
    }

	public void add(String item){
		if(item==null)
			return;
		items.add(item.trim());
	}
	
	public void addAll(ItemList list){
		items.addAll(list.items);
	}
	
	public void addAll(String s){
		this.split(s,sp,items);
	}
	
	public void addAll(String s,String sp){
		this.split(s,sp,items);
	}
	
	public void addAll(String s,String sp,boolean isMultiToken){
        itemListHelper.split(s,sp,items,isMultiToken);
	}
	
	/**
	 * @param p 0-based
	 * @return
	 */
	public String grab(int p){
		return (String)items.get(p);
	}
	
	public int size(){
        return itemListHelper.size();
    }

	public String toString(){
		return toString(sp);
	}
	
	public String toString(String sp){
		StringBuffer sb=new StringBuffer();
		
		for(int p = 0; p <items.size(); p++){
			if(p ==0)
				sb.append(items.get(p));
			else{
				sb.append(sp);
				sb.append(items.get(p));
			}
		}
		return sb.toString();

	}
	
	public void release(){
        itemListHelper.release();
    }
	
	public void reset(){
		sp=",";
		items.clear();
	}
}
