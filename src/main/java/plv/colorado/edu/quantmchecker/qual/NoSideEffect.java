package plv.colorado.edu.quantmchecker.qual;

import org.checkerframework.framework.qual.*;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

/**
 * @author Tianhan Lu
 */
@InvisibleQualifier
@SubtypeOf({Summary.class})
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@ImplicitFor(literals= LiteralKind.NULL)
@Documented
@DefaultQualifierInHierarchy
public @interface SideEffect {
}
