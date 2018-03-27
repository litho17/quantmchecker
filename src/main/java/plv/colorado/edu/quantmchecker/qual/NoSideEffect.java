package plv.colorado.edu.quantmchecker.qual;

import org.checkerframework.framework.qual.*;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

/**
 * @author Tianhan Lu
 */
@InvisibleQualifier
@SubtypeOf({SideEffect.class})
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@Documented
@DefaultQualifierInHierarchy
public @interface NoSideEffect {
}
