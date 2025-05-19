import multiprocessing
import hashlib
import random

import threshold_crypto as tc
import gmpy2
from util import (
    deserialize_ep,
    _ecc_key_to_serializable,
    serialize_pd,
    deserialize_pd,
)
from Crypto.PublicKey import ECC


from primitives import DSA, ElGamalEncryption, NIZK, ChaumPedersenProof
from exceptions import (
    InvalidSignatureException,
    InvalidProofException,
    InvalidWFNProofException,
)
from subroutines import Mixnet


class Voter:
    def __init__(self, curve, id, vote_min, vote_max):
        self.id = id
        self.vote_min = vote_min
        self.vote_max = vote_max
        self.curve = curve

    def choose_vote_value(self):
        self.vote = random.randrange(self.vote_min, self.vote_max)

    def generate_dsa_keys(self):
        dsa = DSA(self.curve)
        self.secret_key, self.public_key = dsa.keygen()

    def generate_trapdoor_keypair(self): #generate x1 and g^x1
        self.ege = ElGamalEncryption(self.curve)
        self.secret_trapdoor_key, self.public_trapdoor_key = self.ege.keygen()

    def generate_antitrapdoor_keypair(self):#generate x2 and g^x2
        self.secret_antitrapdoor_key, self.public_antitrapdoor_key = self.ege.keygen()


    def encrypt_vote(self, teller_public_key):
        self.g_vote = self.curve.raise_p(int(self.vote))
        self.encrypted_vote = self.ege.encrypt(
            teller_public_key.Q, self.g_vote
        )

    def encrypt_antivote(self, teller_public_key):
        self.g_antivote = self.curve.raise_p(int(abs(self.vote-1)))
        self.encrypted_antivote = self.ege.encrypt(
            teller_public_key.Q, self.g_antivote
        )

    def encrypt_trapdoor(self, teller_public_key): #encrypt g^x1
        self.encrypted_trapdoor = self.ege.encrypt(
            teller_public_key.Q, self.public_trapdoor_key
        )

    def encrypt_antitrapdoor(self, teller_public_key):#encrypt g^x2
        self.encrypted_antitrapdoor = self.ege.encrypt(
            teller_public_key.Q, self.public_antitrapdoor_key
        )

    def generate_pok_trapdoor_keypair(self, teller_public_key): #prove that the voter knows g^x1 and r
        encrypted_trapdoor = {
            "c1": self.encrypted_trapdoor[0],
            "c2": self.encrypted_trapdoor[1],
        }
        r = self.encrypted_trapdoor[2]
        chmp = ChaumPedersenProof(self.curve)
        self.pok_trapdoor_key = chmp.prove(
            encrypted_trapdoor,     #enc(g^x1)
            r,
            teller_public_key.Q,
            self.public_trapdoor_key, #g^x1
        )

    def generate_pok_antitrapdoor_keypair(self, teller_public_key):#prove that the voter knows g^x2 and r
        encrypted_antitrapdoor = {
            "c1": self.encrypted_antitrapdoor[0],
            "c2": self.encrypted_antitrapdoor[1],
        }
        r = self.encrypted_antitrapdoor[2]
        chmp = ChaumPedersenProof(self.curve)
        self.pok_antitrapdoor_key = chmp.prove(
            encrypted_antitrapdoor,
            r,
            teller_public_key.Q,
            self.public_antitrapdoor_key,
        )
    def generate_wellformedness_proof(self, teller_public_key):
        encrypted_vote = {
            "c1": self.encrypted_vote[0],
            "c2": self.encrypted_vote[1],
        }
        r = self.encrypted_vote[2]
        chmp = ChaumPedersenProof(self.curve)
        self.wellformedness_proof = chmp.prove_or_n(
            encrypted_vote,
            r,
            teller_public_key.Q,
            self.vote_max,
            int(self.vote),
            self.id,
        )

    def generate_wellformedness_proof_anti(self, teller_public_key):
        encrypted_antivote = {
            "c1": self.encrypted_antivote[0],
            "c2": self.encrypted_antivote[1],
        }
        r = self.encrypted_antivote[2]
        chmp = ChaumPedersenProof(self.curve)
        self.wellformedness_proof_anti = chmp.prove_or_n(
            encrypted_antivote,
            r,
            teller_public_key.Q,
            self.vote_max,
            int(abs(self.vote-1)),
            self.id,
        )


    def sign_ballot(self):
        self.dsa = DSA(self.curve)
        self.sum_r = self.encrypted_vote[2]+self.encrypted_antivote[2]
        hash = self.curve.hash_to_mpz(
            str(self.encrypted_vote)
            + str(self.encrypted_antivote) 
            + str(self.encrypted_trapdoor)
            + str(self.encrypted_antitrapdoor)
            + str(self.pok_trapdoor_key)
            + str(self.pok_antitrapdoor_key)
            + str(self.wellformedness_proof)
            + str(self.wellformedness_proof_anti)
            + str(self.sum_r)    
        )
        self.signature = self.dsa.sign(self.secret_key, hash)
        bb_data = {
            "id": self.id,
            "spk": self.public_key,
            "sig": self.signature,
            # only for poc
            "stk": self.secret_trapdoor_key,
            "stk_anti": self.secret_antitrapdoor_key,
            "ev": self.encrypted_vote,
            "ev_anti": self.encrypted_antivote,
            "enc_ptk": self.encrypted_trapdoor,
            "enc_ptk_anti": self.encrypted_antitrapdoor,
            "pi_1": self.pok_trapdoor_key,
            "pi_1_anti": self.pok_antitrapdoor_key,
            "pi_2": self.wellformedness_proof,
            "pi_3": self.wellformedness_proof_anti,
            "sum_r": self.sum_r,
        }
        return bb_data

    def notify(self, encrypted_term):
        self.g_ri = encrypted_term

    def generate_verification_comm(self):
        g_ri_x = self.g_ri * self.secret_trapdoor_key
        return g_ri_x


class Teller:
    def __init__(self, curve, secret_key_share, public_key):
        self.curve = curve
        self.secret_key_share = secret_key_share
        self.public_key = public_key
        self.ege = ElGamalEncryption(self.curve)
        self.core_count = multiprocessing.cpu_count()

    def generate_threshold_keys(k, num_tellers, tc_key_params):
        thresh_params = tc.ThresholdParameters(k, num_tellers)
        pub_key, key_shares = tc.create_public_key_and_shares_centralized(
            tc_key_params, thresh_params
        )
        return pub_key, key_shares



    def mp_raise_h(self, list_in, q1, q2, q3):
        teller_proofs = []
        teller_registry = []
        list_out = []
        for i in range(0, len(list_in)):
            ballot = list_in[i][1]
            index = list_in[i][0]

            #reenc(g^x1r_i)
            ciphertext, ciphertext_anti, proof, r_i = self.raise_h(self.public_key, ballot)
            ciphertext["c1"] = tc.data._ecc_point_to_serializable(ciphertext["c1"])
            ciphertext["c2"] = tc.data._ecc_point_to_serializable(ciphertext["c2"])
            ciphertext_anti["c1"] = tc.data._ecc_point_to_serializable(ciphertext_anti["c1"])
            ciphertext_anti["c2"] = tc.data._ecc_point_to_serializable(ciphertext_anti["c2"])

            proof[0] = tc.data._ecc_point_to_serializable(proof[0])
            proof[1] = tc.data._ecc_point_to_serializable(proof[1])
            proof[2] = tc.data._ecc_point_to_serializable(proof[2])
            proof[3] = tc.data._ecc_point_to_serializable(proof[3])

            tmp_enc_ptk = [] #enc(g^x1)
            tmp_enc_ptk.append(tc.data._ecc_point_to_serializable(ballot["enc_ptk"][0]))
            tmp_enc_ptk.append(tc.data._ecc_point_to_serializable(ballot["enc_ptk"][1]))

            tmp_enc_ptk_anti = []
            tmp_enc_ptk_anti.append(tc.data._ecc_point_to_serializable(ballot["enc_ptk_anti"][0]))
            tmp_enc_ptk_anti.append(tc.data._ecc_point_to_serializable(ballot["enc_ptk_anti"][1]))
            

            reenc = self.ege.re_encrypt(self.public_key.Q, ballot["ev"])
            nizk = NIZK(self.curve)
            proof_re_enc = nizk.proof_2(
                reenc,
                self.public_key.Q,
                ballot["ev"],
                reenc[2],
            )

            reenc[0] = tc.data._ecc_point_to_serializable(reenc[0])
            reenc[1] = tc.data._ecc_point_to_serializable(reenc[1])

            proof_re_enc["t_1"] = tc.data._ecc_point_to_serializable(proof_re_enc["t_1"])
            proof_re_enc["t_2"] = tc.data._ecc_point_to_serializable(proof_re_enc["t_2"])
            
            y, gy = self.ege.keygen()
            enc_gy = self.ege.encrypt(
            self.public_key.Q, gy) 
           
            enc_gy[0] = tc.data._ecc_point_to_serializable(enc_gy[0])
            enc_gy[1] = tc.data._ecc_point_to_serializable(enc_gy[1])
            
            enc_gr = self.ege.encrypt(
            self.public_key.Q, self.curve.raise_p(r_i)) 
           
            enc_gr[0] = tc.data._ecc_point_to_serializable(enc_gr[0])
            enc_gr[1] = tc.data._ecc_point_to_serializable(enc_gr[1])
            
            s, gs = self.ege.keygen()
            enc_gs = self.ege.encrypt(
            self.public_key.Q, gs) 
           
            enc_gs[0] = tc.data._ecc_point_to_serializable(enc_gs[0])
            enc_gs[1] = tc.data._ecc_point_to_serializable(enc_gs[1])
            


            teller_proof_record = {
                "ev": ballot["ev"],
                "h_r": ciphertext,
                "h_r_anti": ciphertext_anti,
                "proof": proof,
                "enc_ptk" : tmp_enc_ptk,
                "enc_ptk_anti" : tmp_enc_ptk_anti,
                "reenc" : reenc,
                "proof_re_enc" : proof_re_enc,
                "enc_gy" : enc_gy,
                "enc_gr" : enc_gr,
                "enc_gs" : enc_gs,
                "id": ballot["id"],
            }
            teller_proofs.append(teller_proof_record)
            ballot["h_r"] = ciphertext
            ballot["h_r_anti"] = ciphertext_anti
            ballot["proof_h_r"] = proof
            ballot["reenc"] = reenc
            ballot["proof_re_enc"] = proof_re_enc
            ballot["enc_gy"] = enc_gy
            ballot["enc_gr"] = enc_gr
            ballot["enc_gs"] = enc_gs
            teller_registry.append(
                {
                    "id": ballot["id"],
                    "g_r": tc.data._ecc_point_to_serializable(
                        self.curve.raise_p(r_i)
                    ),
                    "enc_ptk" : tmp_enc_ptk,
                    "enc_ptk_anti" : tmp_enc_ptk_anti,
                }
            )
            temp = []
            temp.append(index)

            ballot["spk"] = _ecc_key_to_serializable(ballot["spk"])

            temp_ev = ballot["ev"]
            temp_ev[0] = tc.data._ecc_point_to_serializable(temp_ev[0])
            temp_ev[1] = tc.data._ecc_point_to_serializable(temp_ev[1])
            
            temp_evanti = ballot["ev_anti"]
            temp_evanti[0] = tc.data._ecc_point_to_serializable(temp_evanti[0])
            temp_evanti[1] = tc.data._ecc_point_to_serializable(temp_evanti[1])

            temp_enc_ptk = ballot["enc_ptk"]
            temp_enc_ptk[0] = tc.data._ecc_point_to_serializable(ballot["enc_ptk"][0])
            temp_enc_ptk[1] = tc.data._ecc_point_to_serializable(ballot["enc_ptk"][1])
            
            temp_enc_ptk_anti = ballot["enc_ptk_anti"]
            temp_enc_ptk_anti[0] = tc.data._ecc_point_to_serializable(ballot["enc_ptk_anti"][0])
            temp_enc_ptk_anti[1] = tc.data._ecc_point_to_serializable(ballot["enc_ptk_anti"][1])
            ballot["pi_1"][2] = tc.data._ecc_point_to_serializable(
                ballot["pi_1"][2]
            )
            ballot["pi_1_anti"][2] = tc.data._ecc_point_to_serializable(
                ballot["pi_1_anti"][2]
            )
            ballot["pi_2"][0][0] = tc.data._ecc_point_to_serializable(
                ballot["pi_2"][0][0]
            )
            ballot["pi_2"][0][1] = tc.data._ecc_point_to_serializable(
                ballot["pi_2"][0][1]
            )
            ballot["pi_2"][1][0] = tc.data._ecc_point_to_serializable(
                ballot["pi_2"][1][0]
            )
            ballot["pi_2"][1][1] = tc.data._ecc_point_to_serializable(
                ballot["pi_2"][1][1]
            )
            ballot["pi_3"][0][0] = tc.data._ecc_point_to_serializable(
                ballot["pi_3"][0][0]
            )
            ballot["pi_3"][0][1] = tc.data._ecc_point_to_serializable(
                ballot["pi_3"][0][1]
            )
            ballot["pi_3"][1][0] = tc.data._ecc_point_to_serializable(
                ballot["pi_3"][1][0]
            )
            ballot["pi_3"][1][1] = tc.data._ecc_point_to_serializable(
                ballot["pi_3"][1][1]
            )
            

            temp.append(ballot)
            list_out.append(temp)


        q1.put(teller_proofs)
        q2.put(teller_registry)
        q3.put(list_out)

    def ciphertext_list_split(self, list_0, n):
        k, m = divmod(len(list_0), n)
        split_list = [
            list_0[i * k + min(i, m) : (i + 1) * k + min(i + 1, m)]
            for i in range(n)
        ]
        return split_list

    def tag_ciphertexts(self, list_0):
        list_1 = []
        index = 0
        for item in list_0:
            temp = []
            temp.append(index)
            temp.append(item[0])
            temp.append(item[1])
            temp.append(item[2])
            list_1.append(temp)
            index = index + 1
        return list_1

    def verify_decryption_proof(
        self,
        tau,
        p_1,
        p_2,
        w,
        public_key_share,
        ciphertexts,
        partial_decryptions,
    ):
        prod_alpha = ECC.EccPoint(0, 0, "P-256")
        prod_partial_decryptions = ECC.EccPoint(0, 0, "P-256")
        alpha_terms = []
        for ciphertext in ciphertexts:
            index = ciphertext[0]
            alpha_terms.append(ciphertext[1][0])
            t = (
                gmpy2.mpz(
                    "0x"
                    + hashlib.sha256(
                        str(
                            str(tau) + str(ciphertext[1][0]) + str(index)
                        ).encode("UTF-8")
                    ).hexdigest()
                )
                % self.curve.get_pars().order
            )

            s_2 = ciphertexts[1][0] * t
            prod_alpha = prod_alpha + s_2
        for partial_decryption in partial_decryptions:
            prod_partial_decryptions = (
                prod_partial_decryptions + partial_decryption.v_y
            )
        u = (
            gmpy2.mpz(
                "0x"
                + hashlib.sha256(
                    str(
                        str(p_1)
                        + str(p_1)
                        + str(self.curve.get_pars().P)
                        + str(public_key_share)
                        + str(alpha_terms)
                        + str(partial_decryptions)
                    ).encode("UTF-8")
                ).hexdigest()
            )
            % self.curve.get_pars().order
        )
        v_1 = self.curve.raise_p(w) + (public_key_share * u)
        v_2 = prod_alpha * w
        v_2 = v_2 + (prod_partial_decryptions * u)
        if (p_1 == v_1) and (p_2 == v_2):
            return 1
        return 0

    def mp_partial_decrypt(self, ciphertexts_in, q1, q2, q3, q4):
        #TODO proofs for q3
        tau_1 = self.curve.get_random()
        tau_2 = self.curve.get_random()
        tau_3 = self.curve.get_random()
        r_1 = self.curve.get_random()
        r_2 = self.curve.get_random()
        r_3 = self.curve.get_random()
        p_1_1 = self.curve.raise_p(r_1)
        p_2_1 = self.curve.raise_p(r_2)
        p_3_1 = self.curve.raise_p(r_3)
        comm_tau_1 = hashlib.sha256(str(tau_1).encode("UTF-8")).hexdigest()
        comm_tau_2 = hashlib.sha256(str(tau_2).encode("UTF-8")).hexdigest()
        comm_tau_3 = hashlib.sha256(str(tau_3).encode("UTF-8")).hexdigest()
        output = []
        output2 = []
        output3 = []
        proof = []
        prod_alpha_1 = ECC.EccPoint(0, 0, "P-256")
        prod_alpha_2 = ECC.EccPoint(0, 0, "P-256")
        prod_alpha_3 = ECC.EccPoint(0, 0, "P-256")
        alpha_terms_1 = []
        alpha_terms_2 = []
        alpha_terms_3 = []
        flag = 0
        for ciphertext in ciphertexts_in:
            index = ciphertext[0]
            alpha_1 = ciphertext[1][0]
            alpha_2 = ciphertext[2][0]
            alpha_3 = ciphertext[3][0]
            t_1 = (
                gmpy2.mpz(
                    "0x"
                    + hashlib.sha256(
                        str(str(tau_1) + str(alpha_1) + str(index)).encode(
                            "UTF-8"
                        )
                    ).hexdigest()
                )
                % self.curve.get_pars().order
            )
            t_2 = (
                gmpy2.mpz(
                    "0x"
                    + hashlib.sha256(
                        str(str(tau_2) + str(alpha_2) + str(index)).encode(
                            "UTF-8"
                        )
                    ).hexdigest()
                )
                % self.curve.get_pars().order
            )
            t_3 = (
                gmpy2.mpz(
                    "0x"
                    + hashlib.sha256(
                        str(str(tau_3) + str(alpha_3) + str(index)).encode(
                            "UTF-8"
                        )
                    ).hexdigest()
                )
                % self.curve.get_pars().order
            )

            pd_1 = self.ege.partial_decrypt(
                ECC.EccPoint(
                    ciphertext[1][0]["x"],
                    ciphertext[1][0]["y"],
                    ciphertext[1][0]["curve"],
                ),
                self.secret_key_share,
            )
            pd_2 = self.ege.partial_decrypt(
                ECC.EccPoint(
                    ciphertext[2][0]["x"],
                    ciphertext[2][0]["y"],
                    ciphertext[2][0]["curve"],
                ),
                self.secret_key_share,
            )
            pd_3 = self.ege.partial_decrypt(
                ECC.EccPoint(
                    ciphertext[3][0]["x"],
                    ciphertext[3][0]["y"],
                    ciphertext[3][0]["curve"],
                ),
                self.secret_key_share,
            )
            if flag == 0:
                flag = 1
                prod_alpha_1 = deserialize_ep(alpha_1) * t_1

                prod_alpha_2 = deserialize_ep(alpha_2) * t_2

                prod_alpha_3 = deserialize_ep(alpha_3) * t_3

            else:
                prod_alpha_1 = prod_alpha_1 + (deserialize_ep(alpha_1) * t_1)

                prod_alpha_2 = prod_alpha_2 + (deserialize_ep(alpha_2) * t_2)
                
                prod_alpha_3 = prod_alpha_3 + (deserialize_ep(alpha_3) * t_3)

            alpha_terms_1.append(alpha_1)
            alpha_terms_2.append(alpha_2)
            alpha_terms_3.append(alpha_3)
            
            temp = []
            temp.append(index)
            temp.append(serialize_pd(pd_1))
            output.append(temp)

            temp2 = []
            temp2.append(index)
            temp2.append(serialize_pd(pd_2))
            output2.append(temp2)
            
            temp3 = []
            temp3.append(index)
            temp3.append(serialize_pd(pd_3))
            output3.append(temp3)
        q1.put(output)
        q2.put(output2)
        q3.put(output3)

        p_1_2 = prod_alpha_1 * r_1
        p_2_2 = prod_alpha_2 * r_2
        p_3_2 = prod_alpha_3 * r_3
        u_1 = (
            gmpy2.mpz(
                "0x"
                + hashlib.sha256(
                    str(
                        str(p_1_1)
                        + str(p_1_2)
                        + str(self.curve.get_pars().P.x)
                        + str(self.curve.get_pars().P.y)
                        + str(self.curve.raise_p(self.secret_key_share.y))
                        + str(alpha_terms_1)
                        + str(output)
                    ).encode("UTF-8")
                ).hexdigest()
            )
            % self.curve.get_pars().order
        )

        u_2 = (
            gmpy2.mpz(
                "0x"
                + hashlib.sha256(
                    str(
                        str(p_2_1)
                        + str(p_2_2)
                        + str(self.curve.get_pars().P.x)
                        + str(self.curve.get_pars().P.y)
                        + str(self.curve.raise_p(self.secret_key_share.y))
                        + str(alpha_terms_2)
                        + str(output2)
                    ).encode("UTF-8")
                ).hexdigest()
            )
            % self.curve.get_pars().order
        )

        u_3 = (
            gmpy2.mpz(
                "0x"
                + hashlib.sha256(
                    str(
                        str(p_3_1)
                        + str(p_3_2)
                        + str(self.curve.get_pars().P.x)
                        + str(self.curve.get_pars().P.y)
                        + str(self.curve.raise_p(self.secret_key_share.y))
                        + str(alpha_terms_3)
                        + str(output3)
                    ).encode("UTF-8")
                ).hexdigest()
            )
            % self.curve.get_pars().order
        )
        w_1 = r_1 - (u_1 * self.secret_key_share.y)
        w_2 = r_2 - (u_2 * self.secret_key_share.y)
        w_3 = r_3 - (u_3 * self.secret_key_share.y)
        q4.put(
            {
                "p_1_1": tc.data._ecc_point_to_serializable(p_1_1),
                "p_1_2": tc.data._ecc_point_to_serializable(p_1_2),
                "p_2_1": tc.data._ecc_point_to_serializable(p_2_1),
                "p_2_2": tc.data._ecc_point_to_serializable(p_2_2),
                "p_3_1": tc.data._ecc_point_to_serializable(p_3_1),
                "p_3_2": tc.data._ecc_point_to_serializable(p_3_2),
                "w_1": w_1,
                "w_2": w_2,
                "w_3": w_3,
                "tau_1": tau_1,
                "tau_2": tau_2,
                "tau_3": tau_3,
            }
        )

    def multi_dim_index(self, list, key):
        for item in list:
            if item[0] == key:
                return item
        return None

    def mp_full_decrypt(self, pd1_in, ciphertexts, col, q1):
        result = []
        for item in pd1_in:
            index = item[0]
            ct = self.multi_dim_index(ciphertexts, index)
            ciphertext = tc.EncryptedMessage(
                deserialize_ep(ct[col][0]), deserialize_ep(ct[col][1]), ""
            )

            result.append(
                [
                    index,
                    tc.data._ecc_point_to_serializable(
                        self.ege.threshold_decrypt(
                            item[1],
                            ciphertext,
                            tc.ThresholdParameters(2, 3),
                        )
                    ),
                ]
            )
        q1.put(result)

    def full_decrypt(self, pd_in, q1):
        global decrypted
        split_ciphertexts = self.ciphertext_list_split(pd_in, self.core_count)
        processes = [
            multiprocessing.Process(
                target=self.mp_full_decrypt, args=(ciph, q1)
            )
            for ciph in split_ciphertexts
        ]
        for p in processes:
            p.daemon = True
            p.start()
        data = []
        for p in processes:
            data = data + q1.get()

        for p in processes:
            p.join()
            # p.close()
        decrypted = data

    def validate_ballot(curve, teller_public_key, ballot):
        dsa = DSA(curve)
        hash = curve.hash_to_mpz(
            str(ballot["ev"])
            + str(ballot["ev_anti"])
            + str(ballot["enc_ptk"])
            + str(ballot["enc_ptk_anti"])
            + str(ballot["pi_1"])
            + str(ballot["pi_1_anti"])
            + str(ballot["pi_2"])
            + str(ballot["pi_3"])
            + str(ballot["sum_r"])
        )

        chmp = ChaumPedersenProof(curve)
        ege = ElGamalEncryption(curve)
        try:
            if not dsa.verify(ballot["spk"], ballot["sig"], hash):
                raise InvalidSignatureException(ballot["id"])
            ciphertext_ptk = {"c1": ballot["enc_ptk"][0], "c2": ballot["enc_ptk"][1]}
            if not chmp.verify(ciphertext_ptk,teller_public_key.Q, ballot["pi_1"][0], ballot["pi_1"][1], ballot["pi_1"][2]):
                raise InvalidProofException(ballot["id"])
            ciphertext_ptk_anti = {"c1": ballot["enc_ptk_anti"][0], "c2": ballot["enc_ptk_anti"][1]}
            if not chmp.verify(ciphertext_ptk_anti,teller_public_key.Q, ballot["pi_1_anti"][0], ballot["pi_1_anti"][1], ballot["pi_1_anti"][2]):
                raise InvalidProofException(ballot["id"])
            ciphertext = {"c1": ballot["ev"][0], "c2": ballot["ev"][1]}
            if not chmp.verify_or_n(
                ciphertext,
                teller_public_key.Q,
                ballot["pi_2"][0],
                ballot["pi_2"][1],
                ballot["pi_2"][2],
                ballot["pi_2"][3],
                ballot["id"],
            ):
                raise InvalidWFNProofException(ballot["id"])
            ciphertext_anti = {"c1": ballot["ev_anti"][0], "c2": ballot["ev_anti"][1]}
            if not chmp.verify_or_n(
                ciphertext_anti,
                teller_public_key.Q,
                ballot["pi_3"][0],
                ballot["pi_3"][1],
                ballot["pi_3"][2],
                ballot["pi_3"][3],
                ballot["id"],
            ):
                raise InvalidWFNProofException(ballot["id"])
            mul_cip = [ballot["ev"][0] + ballot["ev_anti"][0], ballot["ev"][1] + ballot["ev_anti"][1], 
                    ballot["sum_r"]] 
            t = ballot["sum_r"]*teller_public_key.Q
            z = -t
            m = mul_cip[1] + z 
            if not(m == curve.get_pars().P): 
                raise InvalidWFNProofException(ballot["id"])
            

        except Exception as e:
            print(e)

    def raise_h(self, teller_public_key, ballot):
        r_i = self.curve.get_random()
        enc_voter_public_key = ballot["enc_ptk"] #enc(g^x1)
        enc_voter_public_key_anti = ballot["enc_ptk_anti"]

        ege = ElGamalEncryption(self.curve)


        re_rand =  [enc_voter_public_key[0] * r_i , enc_voter_public_key[1] * r_i,  r_i]
        re_rand_anti = [enc_voter_public_key_anti[0] * r_i , enc_voter_public_key_anti[1] * r_i,  r_i]

        ciphertext_t = self.ege.re_encrypt(self.public_key.Q, re_rand)
        ciphertext_t_anti = self.ege.re_encrypt(self.public_key.Q, re_rand_anti)

        ciphertext = {"c1" : ciphertext_t[0] , "c2": ciphertext_t[1],   "r": ciphertext_t[3] }
        ciphertext_anti = {"c1" : ciphertext_t_anti[0] , "c2" :  ciphertext_t_anti[1], "r_anti": ciphertext_t_anti[3]}

      
        chmp = ChaumPedersenProof(self.curve)
        #prove that all ciphertexts are raise to r_i and re_encrypted
        proof = chmp.prove_s( 
            ciphertext,     
            r_i,
            ciphertext_t[3],
            enc_voter_public_key, 
            ciphertext_anti,
            enc_voter_public_key_anti,
            ciphertext_t_anti[3],
            teller_public_key.Q,
        )


        return ciphertext, ciphertext_anti, proof,  r_i

    def verify_proof_h_r(curve, enc_ptk , h_r, enc_ptk_anti, h_r_anti,  proof, teller_public_key):
        chmp = ChaumPedersenProof(curve)
        if not chmp.verify_s(h_r,  enc_ptk, h_r_anti, enc_ptk_anti, proof[0], proof[1], proof[2],proof[3], proof[4], proof[5], proof[6], teller_public_key.Q):
            raise InvalidProofException(id)
            print(e)


    def verify_proof_reenc(curve, teller_public_key, h_r, ptk, proof, id):
        nizk = NIZK(curve)
        if not nizk.verify_2(h_r, teller_public_key.Q, ptk, proof):
            raise InvalidProofException(id)
            print(e)

    def re_encryption_mix(self, list_0):
        mx = Mixnet(self.curve)
        proof = mx.re_encryption_mix(list_0, self.public_key.Q)
        return proof

    def verify_re_enc_mix(self, list_0, proof):
        mx = Mixnet(self.curve)
        return mx.verify_mix(
            self.public_key.Q,
            list_0,
            proof[0],
            proof[1],
            proof[2],
            proof[3],
            proof[4],
            proof[5],
            proof[6],
            proof[7],
            proof[8],
            proof[9],
            proof[10],
            proof[11],
            proof[12],
            proof[13],
            proof[14],
            proof[15],
            proof[16],
            proof[17],
            proof[18],
            proof[19],
        )

    def notify(curve, registry_entry):
        ege = ElGamalEncryption(curve)
        g_ri = curve.raise_p(registry_entry["r_i"])
        ciphertext = ege.encrypt(registry_entry["ptk"], g_ri)
        return ciphertext

    def decrypt(curve, registry_entry):
        ege = ElGamalEncryption(curve)
        g_ri = curve.raise_p(registry_entry["r_i"])
        ciphertext = ege.encrypt(registry_entry["ptk"], g_ri)
        return ciphertext

    def individual_board_shuffle(self, list_0):
        key = self.curve.get_random()
        mx = Mixnet(self.curve)
        proof = mx.exponentiation_mix(list_0, key)
        """
        mx.verify_exponentiation_mix(
            list_0,
            proof[0],
            proof[1],
            proof[2],
            proof[3],
            proof[4],
            proof[5],
            proof[6],
            proof[7],
            proof[8],
            proof[9],
            proof[10],
            proof[11],
            proof[12],
            proof[13],
            proof[14],
            proof[15],
        )
        """
        return proof[0], key
