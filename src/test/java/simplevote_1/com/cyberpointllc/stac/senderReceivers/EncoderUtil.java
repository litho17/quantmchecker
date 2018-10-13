package simplevote_1.com.cyberpointllc.stac.senderReceivers;

import simplevote_1.com.cyberpointllc.stac.algorithm.CipherPublicKey;
import simplevote_1.com.cyberpointllc.stac.algorithm.CipherUtil;
import simplevote_1.com.cyberpointllc.stac.proto.Comms;
import com.google.protobuf.ByteString;

import java.math.BigInteger;

/**
 * Serializes and deserializes Comms messages
 */
public class EncoderUtil {

    public static CipherPublicKey deserializePublicKey(Comms.PublicKey publicKey) {
        byte[] e = publicKey.getE().toByteArray();
        byte[] floormod = publicKey.getModulus().toByteArray();
        return new CipherPublicKey(CipherUtil.toBigInt(floormod), CipherUtil.toBigInt(e));
    }

    public static BigInteger deserializeDHPublicKey(Comms.DHPublicKey publicKey) {
        byte[] publicKeyByte = publicKey.getKey().toByteArray();
        return CipherUtil.toBigInt(publicKeyByte);
    }

    public static Comms.DHPublicKey serializeDHPublicKey(BigInteger publicKey) {
        Comms.DHPublicKey dhPublicKey = Comms.DHPublicKey.newBuilder()
                .setKey(ByteString.copyFrom(publicKey.toByteArray()))
                .build();
        return dhPublicKey;
    }

    public static ProtocolsNetworkAddress deserializeNetworkAddress(Comms.NetworkAddress networkAddressMsg) {
        String origin = networkAddressMsg.getHost();
        int port = networkAddressMsg.getPort();
        return new ProtocolsNetworkAddress(origin, port);
    }

    public static Comms.NetworkAddress serializeNetworkAddress(ProtocolsNetworkAddress callbackAddress) {
        if (callbackAddress == null) {
            return null;
        }

        Comms.NetworkAddress address = Comms.NetworkAddress.newBuilder()
                .setHost(callbackAddress.obtainOrigin())
                .setPort(callbackAddress.takePort())
                .build();

        return address;
    }

    public static Comms.Identity serializeUnity(ProtocolsPublicUnity unity) {
        Comms.Identity.Builder serializedIdCreator = Comms.Identity.newBuilder()
                .setId(unity.getId())
                .setPublicKey(unity.pullPublicKey().serializePublicKey());

        if (unity.hasCallbackAddress()) {
            serializedIdCreator.setCallbackAddress(serializeNetworkAddress(unity.fetchCallbackAddress()));
        }

        return serializedIdCreator.build();
    }

    public static ProtocolsPublicUnity deserializeUnity(Comms.Identity unity) {
        String id = unity.getId();
        Comms.PublicKey publicKey = unity.getPublicKey();
        CipherPublicKey CipherPublicKey = deserializePublicKey(publicKey);

        if (unity.hasCallbackAddress()) {
            return new ProtocolsPublicUnity(id, CipherPublicKey, deserializeNetworkAddress(unity.getCallbackAddress()));
        }

        return new ProtocolsPublicUnity(id, CipherPublicKey);
    }
}
