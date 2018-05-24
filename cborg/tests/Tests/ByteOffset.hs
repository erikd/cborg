{-# LANGUAGE DeriveFunctor, BangPatterns #-}

module Tests.ByteOffset where

import           Data.Word
--import           Numeric.Half (Half)
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import           Control.Exception (throw)

import           Codec.CBOR.Decoding
import           Codec.CBOR.Read (deserialiseFromBytes)
import qualified Codec.CBOR.Term as Term (Term(..))

--import qualified Tests.Reference.Implementation as RefImpl
import qualified Tests.CBOR {- (eqTerm) -} as Test
import           Tests.CBOR (eqTerm)

import Prelude hiding (encodeFloat, decodeFloat)


-- | Like a 'Term.Term', but with an annotation on top level terms and every
-- subterm. This is used for tests of 'peekByteOffset' where we annotate a
-- decoded term with the byte range it covers.
--
data AnnTerm ann = AnnTerm (TermF (AnnTerm ann)) ann
  deriving (Show, Eq, Functor)

data TermF t = TInt     Int
             | TInteger Integer
             | TBytes   BS.ByteString
             | TBytesI  LBS.ByteString
             | TString  T.Text
             | TStringI LT.Text
             | TList    [t]
             | TListI   [t]
             | TMap     [(t, t)]
             | TMapI    [(t, t)]
             | TTagged  Word64 t
             | TBool    Bool
             | TNull
             | TSimple  Word8
             | THalf    Float
             | TFloat   Float
             | TDouble  Double
  deriving (Show, Eq, Functor)


--------------------------------------------------------------------------------
-- Properties
--

-- | Basic property to check that 'AnnTerm' is isomorphic to the 'Term.Term'.
--
prop_AnnTerm_isomorphic :: Term.Term -> Bool
prop_AnnTerm_isomorphic t =
    t `eqTerm` convertAnnTermToTerm (convertTermToAnnTerm t)
    -- eq including NaNs

prop_peekByteOffset :: Term.Term -> Bool
prop_peekByteOffset t =
    annotationsDecodeToTerm (annTermOffsetsToBytes bytes annt)
  where
    bytes = Test.serialise t
    annt  = deserialise bytes

deserialise :: LBS.ByteString -> AnnTermOffsets
deserialise = either throw snd . deserialiseFromBytes decodeAnnTerm

annotationsDecodeToTerm :: AnnTermBytes -> Bool
annotationsDecodeToTerm t =
    and [ Test.deserialise bs `eqTerm` convertAnnTermToTerm t'
        | t'@(AnnTerm _ bs) <- annotatedSubterms t ]

annotatedSubterms :: AnnTerm a -> [AnnTerm a]
annotatedSubterms at@(AnnTerm t0 _) = at : subterms t0
  where
    subterms :: TermF (AnnTerm a) -> [AnnTerm a]
    subterms (TList  ts)  = concatMap annotatedSubterms ts
    subterms (TListI ts)  = concatMap annotatedSubterms ts
    subterms (TMap   ts)  = [ t' | (x, y) <- ts
                                 , t' <- annotatedSubterms x
                                      ++ annotatedSubterms y ]
    subterms (TMapI  ts)  = [ t' | (x, y) <- ts
                                 , t' <- annotatedSubterms x
                                      ++ annotatedSubterms y ]
    subterms (TTagged _ t') = annotatedSubterms t'

    subterms TInt    {} = []
    subterms TInteger{} = []
    subterms TBytes  {} = []
    subterms TBytesI {} = []
    subterms TString {} = []
    subterms TStringI{} = []
    subterms TBool   {} = []
    subterms TNull   {} = []
    subterms TSimple {} = []
    subterms THalf   {} = []
    subterms TFloat  {} = []
    subterms TDouble {} = []


--------------------------------------------------------------------------------
-- Decoding a term, annotated with its underlying bytes
--

type AnnTermOffsets = AnnTerm (ByteOffset, ByteOffset)
type AnnTermBytes   = AnnTerm  LBS.ByteString

type TermFOffsets = TermF AnnTermOffsets
type TermFBytes   = TermF AnnTermBytes

annTermOffsetsToBytes :: LBS.ByteString -> AnnTermOffsets -> AnnTermBytes
annTermOffsetsToBytes original =
    fmap (`slice` original)
  where
    slice :: (Word, Word) -> LBS.ByteString -> LBS.ByteString
    slice (n,m) = LBS.take (fromIntegral (m-n)) . LBS.drop (fromIntegral n) 


decodeAnnTerm :: Decoder s AnnTermOffsets
decodeAnnTerm = do
    start <- peekByteOffset
    t     <- decodeTermFAnnTerm
    end   <- peekByteOffset
    return (AnnTerm t (start, end))

decodeTermFAnnTerm :: Decoder s (TermF AnnTermOffsets)
decodeTermFAnnTerm = do
    tkty <- peekTokenType
    case tkty of
      TypeUInt   -> do w <- decodeWord
                       return $! fromWord w
                    where
                      fromWord :: Word -> TermFOffsets
                      fromWord w
                        | w <= fromIntegral (maxBound :: Int)
                                    = TInt     (fromIntegral w)
                        | otherwise = TInteger (fromIntegral w)

      TypeUInt64 -> do w <- decodeWord64
                       return $! fromWord64 w
                    where
                      fromWord64 w
                        | w <= fromIntegral (maxBound :: Int)
                                    = TInt     (fromIntegral w)
                        | otherwise = TInteger (fromIntegral w)

      TypeNInt   -> do w <- decodeNegWord
                       return $! fromNegWord w
                    where
                      fromNegWord w
                        | w <= fromIntegral (maxBound :: Int)
                                    = TInt     (-1 - fromIntegral w)
                        | otherwise = TInteger (-1 - fromIntegral w)

      TypeNInt64 -> do w <- decodeNegWord64
                       return $! fromNegWord64 w
                    where
                      fromNegWord64 w
                        | w <= fromIntegral (maxBound :: Int)
                                    = TInt     (-1 - fromIntegral w)
                        | otherwise = TInteger (-1 - fromIntegral w)

      TypeInteger -> do !x <- decodeInteger
                        return (TInteger x)
      TypeFloat16 -> do !x <- decodeFloat
                        return (THalf x)
      TypeFloat32 -> do !x <- decodeFloat
                        return (TFloat x)
      TypeFloat64 -> do !x <- decodeDouble
                        return (TDouble x)

      TypeBytes        -> do !x <- decodeBytes
                             return (TBytes x)
      TypeBytesIndef   -> decodeBytesIndef >> decodeBytesIndefLen []
      TypeString       -> do !x <- decodeString
                             return (TString x)
      TypeStringIndef  -> decodeStringIndef >> decodeStringIndefLen []

      TypeListLen      -> decodeListLen      >>= flip decodeListN []
      TypeListLen64    -> decodeListLen      >>= flip decodeListN []
      TypeListLenIndef -> decodeListLenIndef >>  decodeListIndefLen []
      TypeMapLen       -> decodeMapLen       >>= flip decodeMapN []
      TypeMapLen64     -> decodeMapLen       >>= flip decodeMapN []
      TypeMapLenIndef  -> decodeMapLenIndef  >>  decodeMapIndefLen []
      TypeTag          -> do !x <- decodeTag64
                             !y <- decodeAnnTerm
                             return (TTagged x y)
      TypeTag64        -> do !x <- decodeTag64
                             !y <- decodeAnnTerm
                             return (TTagged x y)

      TypeBool    -> do !x <- decodeBool
                        return (TBool x)
      TypeNull    -> TNull   <$  decodeNull
      TypeSimple  -> do !x <- decodeSimple
                        return (TSimple x)
      TypeBreak   -> fail "unexpected break"
      TypeInvalid -> fail "invalid token encoding"


decodeBytesIndefLen :: [BS.ByteString] -> Decoder s TermFOffsets
decodeBytesIndefLen acc = do
    stop <- decodeBreakOr
    if stop then return $! TBytesI (LBS.fromChunks (reverse acc))
            else do !bs <- decodeBytes
                    decodeBytesIndefLen (bs : acc)


decodeStringIndefLen :: [T.Text] -> Decoder s TermFOffsets
decodeStringIndefLen acc = do
    stop <- decodeBreakOr
    if stop then return $! TStringI (LT.fromChunks (reverse acc))
            else do !str <- decodeString
                    decodeStringIndefLen (str : acc)


decodeListN :: Int -> [AnnTermOffsets] -> Decoder s TermFOffsets
decodeListN !n acc =
    case n of
      0 -> return $! TList (reverse acc)
      _ -> do !t <- decodeAnnTerm
              decodeListN (n-1) (t : acc)


decodeListIndefLen :: [AnnTermOffsets] -> Decoder s TermFOffsets
decodeListIndefLen acc = do
    stop <- decodeBreakOr
    if stop then return $! TListI (reverse acc)
            else do !tm <- decodeAnnTerm
                    decodeListIndefLen (tm : acc)


decodeMapN :: Int -> [(AnnTermOffsets, AnnTermOffsets)] -> Decoder s TermFOffsets
decodeMapN !n acc =
    case n of
      0 -> return $! TMap (reverse acc)
      _ -> do !tm   <- decodeAnnTerm
              !tm'  <- decodeAnnTerm
              decodeMapN (n-1) ((tm, tm') : acc)


decodeMapIndefLen :: [(AnnTermOffsets, AnnTermOffsets)] -> Decoder s TermFOffsets
decodeMapIndefLen acc = do
    stop <- decodeBreakOr
    if stop then return $! TMapI (reverse acc)
            else do !tm  <- decodeAnnTerm
                    !tm' <- decodeAnnTerm
                    decodeMapIndefLen ((tm, tm') : acc)


--------------------------------------------------------------------------------
-- Converting between terms and annotated terms


convertTermToAnnTerm :: Term.Term -> AnnTerm ()
convertTermToAnnTerm t = AnnTerm (convertTermToTermF t) ()

convertTermToTermF :: Term.Term -> TermF (AnnTerm ())
convertTermToTermF (Term.TList  ts)  = TList  (map convertTermToAnnTerm ts)
convertTermToTermF (Term.TListI ts)  = TListI (map convertTermToAnnTerm ts)
convertTermToTermF (Term.TMap    ts)  = TMap  [ ( convertTermToAnnTerm x
                                                   , convertTermToAnnTerm y )
                                                 | (x, y) <- ts ]
convertTermToTermF (Term.TMapI   ts)  = TMapI [ ( convertTermToAnnTerm x
                                                   , convertTermToAnnTerm y )
                                                 | (x, y) <- ts ]
convertTermToTermF (Term.TTagged x t) = TTagged x (convertTermToAnnTerm t)

convertTermToTermF (Term.TInt    x)  = TInt   x
convertTermToTermF (Term.TInteger  x)  = TInteger x
convertTermToTermF (Term.TBytes   x)  = TBytes  x
convertTermToTermF (Term.TBytesI  x)  = TBytesI x
convertTermToTermF (Term.TString  x)  = TString  x
convertTermToTermF (Term.TStringI x)  = TStringI x
convertTermToTermF (Term.TBool    x)  = TBool x
convertTermToTermF  Term.TNull        = TNull
convertTermToTermF (Term.TSimple  x)  = TSimple x
convertTermToTermF (Term.THalf x)  = THalf x
convertTermToTermF (Term.TFloat x)  = TFloat x
convertTermToTermF (Term.TDouble x)  = TDouble x

convertAnnTermToTerm :: AnnTerm a -> Term.Term
convertAnnTermToTerm (AnnTerm t _ann) = convertTermFToTerm t

convertTermFToTerm :: TermF (AnnTerm a) -> Term.Term
convertTermFToTerm (TList  ts)  = Term.TList  (map convertAnnTermToTerm ts)
convertTermFToTerm (TListI ts)  = Term.TListI (map convertAnnTermToTerm ts)
convertTermFToTerm (TMap    ts)  = Term.TMap  [ ( convertAnnTermToTerm x
                                                   , convertAnnTermToTerm y )
                                                 | (x, y) <- ts ]
convertTermFToTerm (TMapI   ts)  = Term.TMapI [ ( convertAnnTermToTerm x
                                                   , convertAnnTermToTerm y )
                                                 | (x, y) <- ts ]
convertTermFToTerm (TTagged x t) = Term.TTagged x (convertAnnTermToTerm t)
convertTermFToTerm (TInt     x)  = Term.TInt   x
convertTermFToTerm (TInteger  x)  = Term.TInteger x
convertTermFToTerm (TBytes   x)  = Term.TBytes  x
convertTermFToTerm (TBytesI  x)  = Term.TBytesI x
convertTermFToTerm (TString  x)  = Term.TString  x
convertTermFToTerm (TStringI x)  = Term.TStringI x
convertTermFToTerm (TBool    x)  = Term.TBool x
convertTermFToTerm  TNull        = Term.TNull
convertTermFToTerm (TSimple  x)  = Term.TSimple x
convertTermFToTerm (THalf x)  = Term.THalf x
convertTermFToTerm (TFloat x)  = Term.TFloat x
convertTermFToTerm (TDouble x)  = Term.TDouble x

