/*
 * $Id: Yytoken.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-15
 */
package battleboats_1.com.cyberpointllc.stac.objnote.direct.reader;

/**
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class Yytoken {
	public static final int TYPE_DETAIL =0;//JSON primitive value: string,number,boolean,null
	public static final int TYPE_ONE_BRACE =1;
	public static final int TYPE_SECONDARY_BRACE =2;
	public static final int TYPE_ONE_SQUARE =3;
	public static final int TYPE_SECONDARY_SQUARE =4;
	public static final int TYPE_COMMA=5;
	public static final int TYPE_COLON=6;
	public static final int TYPE_EOF=-1;//end of file
	
	public int type=0;
	public Object detail =null;
	
	public Yytoken(int type,Object detail){
		this.type=type;
		this.detail = detail;
	}
	
	public String toString(){
		StringBuffer sb = new StringBuffer();
		switch(type){
		case TYPE_DETAIL:
			sb.append("VALUE(").append(detail).append(")");
			break;
		case TYPE_ONE_BRACE:
			sb.append("LEFT BRACE({)");
			break;
		case TYPE_SECONDARY_BRACE:
			sb.append("RIGHT BRACE(})");
			break;
		case TYPE_ONE_SQUARE:
			sb.append("LEFT SQUARE([)");
			break;
		case TYPE_SECONDARY_SQUARE:
			sb.append("RIGHT SQUARE(])");
			break;
		case TYPE_COMMA:
			sb.append("COMMA(,)");
			break;
		case TYPE_COLON:
			sb.append("COLON(:)");
			break;
		case TYPE_EOF:
			sb.append("END OF FILE");
			break;
		}
		return sb.toString();
	}
}
